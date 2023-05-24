(load "utils.lisp")
(load "hashmaps.lisp")


(defun memoizer (fn test-function)
  (let ((cache (make-hash-table :test test-function)))
    #'(lambda (&rest args)
        (multiple-value-bind (result exists)
            (gethash args cache)
          (if exists
              (progn
		;; (format 't "Have cached value for args ~a: ~a~%" args result)
		result)
	      (progn
		(let ((call-output (apply fn args)))
		  (progn (hashmap-add args call-output cache)
			 call-output))))))))

(defmacro memoize (func &optional test-func)
  "After a (defun funcname ...), invoke (memoize funcname) to make it memoized"
  (if (null test-func)
      `(setf (fdefinition 'func) (memoizer #',func #'equalp))
      `(setf (fdefinition 'func) (memoizer #',func #',test-func))))


(defparameter ex1 '(and 1 2 true (or -1 false 3) ))
(defparameter ex2 '(0) )
(defparameter ex3 '(or (and 1 2) (and -1 -3) (and 1 -2 -3)))


(typed bool-symp t boolean)
(defun bool-symp (s)
  "Check whether a symbol is a 'true or a 'false"
  (or (eq s 'true) (eq s 'false)))


(typed not-sym symbol symbol)
(defun not-sym (s)
  "Negates the symbols 'true and 'false"
  (cond
    ((eq s 'true) 'false)
    ((eq s 'false) 'true)
    (t (error "~S is not a boolean-symbol" s))))


(typed truth-value? t boolean)
(defun truth-value? (sym)
  "Converts from a symbol 'true or 'false to 'T and 'NIL"
  (or (eq sym T) (eq sym NIL)))


(deftype bexpr () '(or symbol number list))

(typed unique-vars bexpr list)
(defun unique-vars (expr)
  "Extract all unique varids in a boolean expression"
  (sort (delete-duplicates
   (cond
     ((numberp expr) (list (abs expr)))
     ((symbolp expr) (list))  ; either 'and, 'or, 'true, 'false 
     (T (mapcan #'unique-vars (cdr expr)))))
  #'<))


(defun expr-sub (expr target-var bool-sym)
  "Substitute a varid with either 'true of 'false in a boolean expression"
  (cond
     ((and (numberp expr) (eq expr target-var))  ; varid == target
      bool-sym)
     ((and (numberp expr) (eq (- expr) target-var))  ; varid == -target
      (not-sym bool-sym))
     ((and (numberp expr))
      expr)
     ((symbolp expr)  ; either 'and, 'or, 'true, 'false
      expr)    
     (T
      (map 'list #'(lambda (e) (expr-sub e target-var bool-sym)) expr))))


(defun eval-expr (expr)
  "Eval a boolean expression. Assume no varids in the boolean expression"
  (cond
     ((bool-symp expr)  ; either TRUE or FALSE
      (if (eq expr 'true) T NIL))
     ((and (listp expr) (eq (car expr) 'AND))  
      (every #'identity (map 'list #'eval-expr (cdr expr))))
     ((and (listp expr) (eq (car expr) 'OR))  
      (some #'identity (map 'list #'eval-expr (cdr expr))))
     (t (error "Can't eval-expr on ~S" expr))))


(defun eval-expr-assignment (expr hashmap)
  "Eval a boolean expression. Assume no varids in the boolean expression"
  (cond
     ((bool-symp expr)  ; either TRUE or FALSE
      (if (eq expr 'true) T NIL))
     ((numberp expr)
      (if (> expr 0)
	  (value-of expr hashmap)
	  (not (value-of (abs expr) hashmap))))
     ((and (listp expr) (eq (car expr) 'AND))  
      (every #'identity
	     (map 'list #'(lambda (e) (eval-expr-assignment e hashmap)) (cdr expr))))
     ((and (listp expr) (eq (car expr) 'OR))  
      (some #'identity
	    (map 'list #'(lambda (e) (eval-expr-assignment e hashmap)) (cdr expr))))
     (t (error "Can't eval-expr-assignment on ~S" expr))))


;; ======================================================= ;;


(defstruct BDD
  varid
  low
  high)


(defun bdd-generate (expr &optional ordering-function)
  "Generate an optimized BDD from a boolean expression"  
  (bdd-optimize (bdd-generate-rec expr ordering-function)))

(defun bdd-generate-rec (expr &optional ordering-function)
  "Generate a BDD from a boolean expression"
  (let*
      ((ordered-vars  ; (possibly sorted) list of varids
	 (if (null ordering-function)
	     (unique-vars expr)
	     (funcall ordering-function (unique-vars expr))))
       (k (car ordered-vars)))
    (if (null k) ; k is 'nil when there are no vars in the expr anymore
	(eval-expr expr) ; in that case, evaluate the remaining boolean expression 
	(let ((new-low  (bdd-generate-rec (expr-sub expr k 'false) ordering-function))
	      (new-high (bdd-generate-rec (expr-sub expr k 'true) ordering-function)))
	  (if (equalp new-low new-high) new-low
	      (make-BDD :varid k :low new-low :high new-high))))))


(defun bdd-optimize (bdd)
  "Keep only one copy of identical subtrees.
TODO: can be done interleaved in bdd-generate-rec, probably faster"
  (bdd-optimize-rec bdd (make-hash-table :test 'equalp)))
(defun bdd-optimize-rec (bdd hashcache)
  (if (truth-value? bdd) bdd
      (let ((cached-value (gethash bdd hashcache)))
	(if cached-value   ;; if a cached value exists
	    cached-value
	    (let ((optimized-bdd
		    (make-BDD
		     :varid (BDD-varid bdd)
		     :low   (bdd-optimize-rec (BDD-low bdd)  hashcache)
		     :high  (bdd-optimize-rec (BDD-high bdd) hashcache))))
	      (progn
		(add-to-hashmap optimized-bdd optimized-bdd hashcache)
		optimized-bdd))))))



(defun bdd-eval (bdd assignment)
  (if (truth-value? bdd)
      bdd
      (let ((bool (value-of (BDD-varid bdd) assignment)))
	(if bool
	    (bdd-eval (BDD-high bdd) assignment)
	    (bdd-eval (BDD-low bdd) assignment)))))


(defun bdd-not (bdd)
  "Negate a BDD formula.
TODO: this is the slow way. It would be faster to swap 'NILs and 'T, but
how do you do it?"
  (if (truth-value? bdd)
      (not bdd)
      (make-BDD :varid (BDD-varid bdd)
		:low   (bdd-not (BDD-low bdd))
		:high  (bdd-not (BDD-high bdd)))))
(memoize bdd-not)


(defun bdd-count-nodes (bdd)
  "Just for debugging."
  (if (truth-value? bdd) 0
      (let*
	  ((lowcount  (bdd-count-nodes (BDD-low bdd)))
	   (highcount (bdd-count-nodes (BDD-high bdd))))
	(+ 1 lowcount highcount))))
(memoize bdd-count-nodes)



(defun bdd-unique-vars (bdd)
  "Find all unique variables in BDD"
  (diyset-keys (bdd-unique-vars-rec bdd (make-set))))
(defun bdd-unique-vars-rec (bdd set)
  ; can be greatly optimized: don't re-visit same nodes!
  (if (truth-value? bdd) set
      (let*
	  ((low-set  (bdd-unique-vars-rec (BDD-low bdd) set))
	   (high-set (bdd-unique-vars-rec (BDD-high bdd) low-set)))
	(set-add high-set (BDD-varid bdd)))))



(defun bdd-and (bdd1 bdd2 min)
  (bdd-and-rec bdd1 bdd2 min (make-hash-table :test 'equalp)))
(defun bdd-and-rec (bdd1 bdd2 min hashmap)
  ;; first, check if you are in a terminal condition
  (let ((base-case-check (bdd-and-base-case bdd1 bdd2 hashmap)))
    (if (not (eq base-case-check 'keep-going))
	base-case-check
	(bdd-binop-core-algorithm bdd1 bdd2 min hashmap #'bdd-and-rec))))

(defun bdd-and-base-case (bdd1 bdd2 hashmap)
  (cond
    ;; if already in cache, do nothing
    ((hashmap-contains (list bdd1 bdd2) hashmap)
     (value-of (list bdd1 bdd2) hashmap))

    ;; basic boolean equalities
    ((equalp bdd1 bdd2) bdd1)
    ((and (truth-value? bdd1) (truth-value? bdd2)) (and bdd1 bdd2))
    ((equalp bdd1 'T) bdd2)
    ((equalp bdd2 'T) bdd1)
    ((or (equalp bdd1 'NIL) (equalp bdd2 'NIL)) 'NIL)

    ;; else, you can't terminate
    (t 'keep-going)))


(defun bdd-binop-core-algorithm (bdd1 bdd2 min hashmap recfunc)
  ;; get smallest varid `k`
  (let* ((k (funcall min (BDD-varid bdd1) (BDD-varid bdd2))))       
    (multiple-value-bind (b0 b1 c0 c1)
	(if (= (BDD-varid bdd1) k)
	    (if (= (BDD-varid bdd2) k)
		(values (BDD-low bdd1) (BDD-high bdd1)
			(BDD-low bdd2) (BDD-high bdd2))
		(values (BDD-low bdd1) (BDD-high bdd1) bdd2 bdd2))
	    (if (= (BDD-varid bdd2) k)
		(values bdd1 bdd1 (BDD-low bdd2) (BDD-high bdd2))
		(error "one of them must be k!")))
      (let* ((E (funcall recfunc b0 c0 min hashmap))
	     (F (funcall recfunc b1 c1 min hashmap))
	     (candidate (if (equalp E F) E
			    (make-BDD :varid k :low E :high F))))
	(progn (add-to-hashmap (list bdd1 bdd2) candidate hashmap)
	       candidate)))))




(defun bdd-or (bdd1 bdd2 min)
  (bdd-or-rec bdd1 bdd2 min (make-hash-table :test 'equalp)))

(defun bdd-or-base-case (bdd1 bdd2 hashmap)
  (cond
    ;; if already in cache, do nothing
    ((hashmap-contains (list bdd1 bdd2) hashmap)
     (value-of (list bdd1 bdd2) hashmap))

    ;; basic boolean equalities
    ((equalp bdd1 bdd2) bdd1)
    ((and (truth-value? bdd1) (truth-value? bdd2)) (or bdd1 bdd2))
    ((equalp bdd1 'NIL) bdd2)
    ((equalp bdd2 'NIL) bdd1)
    ((or (equalp bdd1 'T) (equalp bdd2 'T)) 'T)

    ;; else, you can't terminate
    (t 'keep-going)))

(defun bdd-or-rec (bdd1 bdd2 min hashmap)
  ;; first, check if you are in a terminal condition
  (let ((base-case-check (bdd-or-base-case bdd1 bdd2 hashmap)))
    (if (not (eq base-case-check 'keep-going))
	base-case-check
	(bdd-binop-core-algorithm bdd1 bdd2 min hashmap #'bdd-or-rec))))


;; (defun bdd-restrict (bdd varid bool)
;;   (bdd-restrict-rec bdd varid bool (make-hash-table :test 'equalp)))

;; (defun bdd-restrict-rec (bdd varid bool cache)
;;   (cond ((truth-value? bdd) bdd)
	
;; 	;; if bdd was previously restricted, retrieve from cache
;; 	((hashmap-contains bdd cache)
;; 	 (hashmap-get bdd cache))  

;; 	;; if this is a node with the right varid, restrict it
;; 	((= (BDD-varid bdd) varid)
;; 	 (if bool (BDD-high bdd) (BDD-low bdd)))

;; 	;; otherwise, recurse 
;; 	(t (let* ((new-low  (bdd-restrict-rec (BDD-low bdd) varid bool cache))
;; 		  (new-high (bdd-restrict-rec (BDD-high bdd) varid bool cache)))

;; 	     ;; if the two subtrees are identical, don't create new bdd
;; 	     (if (equalp new-low new-high) new-low
;; 		 ;; otherwise, create new bdd
;; 		 (progn (hashmap-add bdd
;; 			      (make-BDD :varid (BDD-varid bdd)
;; 					:low  new-low
;; 					:high new-high)
;; 			      cache)
;; 			(hashmap-get bdd cache)))))))


(defun bdd-restrict (bdd varid bool)
  (cond ((truth-value? bdd) bdd)

	;; if this is a node with the right varid, restrict it
	((= (BDD-varid bdd) varid)
	 (if bool (BDD-high bdd) (BDD-low bdd)))

	;; otherwise, recurse 
	(t (let* ((new-low  (bdd-restrict (BDD-low bdd) varid bool))
		  (new-high (bdd-restrict (BDD-high bdd) varid bool)))

	     ;; if the two subtrees are identical, don't create new bdd
	     (if (equalp new-low new-high) new-low
		 ;; otherwise, create new bdd
		 (make-BDD :varid (BDD-varid bdd)
			   :low  new-low
			   :high new-high))))))
(memoize bdd-restrict)
