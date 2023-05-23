(load "utils.lisp")

(defparameter ex1 '(and 1 2 true (or -1 false 3) ))
(defparameter ex2 '(0) )


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
  "Generate a BDD from a boolean expression"
  (let*
      ((ordered-vars
	 (if (null ordering-function)
	     (unique-vars expr)
	     (funcall ordering-function (unique-vars expr))))
       (k (car ordered-vars)))
    (if (null k)
	(eval-expr expr)
	(make-BDD
	 :varid k
	 :low   (bdd-generate (expr-sub expr k 'false) ordering-function)
	 :high  (bdd-generate (expr-sub expr k 'true) ordering-function)))))

(defparameter bdd1 (bdd-generate '(or 1 (and 2 -3))))
(defparameter bdd2 (bdd-generate '(or 1 (and 2 -3))))
(defparameter bdd3 bdd2)



(defun bdd-eval (bdd assignment)
  (if (truth-value? bdd)
      bdd
      (let ((bool (value-of (BDD-varid bdd) assignment)))
	(if bool
	    (bdd-eval (BDD-high bdd) assignment)
	    (bdd-eval (BDD-low bdd) assignment)))))


(defun bdd-optimize (bdd)
  "Keep only one copy of identical subtrees"
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
	      


(defun bdd-not (bdd)
  (if (truth-value? bdd)
      (not bdd)
      (make-BDD :varid (BDD-varid bdd)
		:low   (bdd-not (BDD-low bdd))
		:high  (bdd-not (BDD-high bdd)))))


(defun bdd-count-nodes (bdd)
  (bdd-count-nodes-rec bdd (make-hash-table :test 'eq)))
(defun bdd-count-nodes-rec (bdd hashmap)
  (if (truth-value? bdd) 0
      (let ((cached-value (gethash bdd hashmap)))
	(if cached-value 0
	    (let*
		((lowcount  (bdd-count-nodes-rec (BDD-low bdd) hashmap))
		 (highcount (bdd-count-nodes-rec (BDD-high bdd) hashmap)))
	      (progn
		(add-to-hashmap bdd 't hashmap)
		(+ 1 lowcount highcount)))))))

'(or (and 1 2) (and -1 -3) (and 1 -2 -3))


;; ================ TESTING ========================== ;;

(defun random-sign () (if (>= (random 1.0) 0.5) 1 -1))
(defun random-varid () (* (random-sign) (+ 1 (random 10))))
(defun random-expr (depth)
  (if (<= depth 0)
      (random-varid)
      (let ((r (random 1.0)))
	(cond
	  ((< r 0.2)
	   (random-varid))
	  ((< r 0.6)
	   (cons 'and
		 (loop repeat (+ 2 (random 4))
		       collect (random-expr (- depth 1)))))
	  ((<= r 1.0)
	   (cons 'or
		 (loop repeat (+ 2 (random 4))
		       collect (random-expr (- depth 1)))))
	  ))))


(defun tester-compare-bdd-expr ()
  "Test whether the eval of a random bexpr and relative BDD are equal"
  (let*
      ((expr (random-expr 1))
       (bdd  (bdd-generate expr)))    
    (loop for hashmap in (assignments (unique-vars expr)) do
      (let
	  ((eval-on-expr (eval-expr-assignment expr hashmap))
	   (eval-on-bdd  (bdd-eval bdd hashmap)))
	(if (not (eq eval-on-expr eval-on-bdd))
	    (format t
		    (concatenate 'string
		     "~%=========================~%"
		     "Expression:~%~a ~%BDD:~%~a ~%Assignment:~%~a ~%~a ~a~%")
		    expr
		    bdd
		    (print-hashmap hashmap)
		    eval-on-expr
		    eval-on-bdd))))))


(defun tester-optimized-bdd-has-less-nodes ()
  "Number of nodes in optimized BDD must be <= than unoptimized BDD"
  (let*
      ((expr (random-expr 2))
       (bdd  (bdd-generate expr))
       (bdd-opt (bdd-optimize bdd)))
    (if (not (<= (bdd-count-nodes bdd-opt) (bdd-count-nodes bdd)))
	(format t
		(concatenate 'string
			     "~%=========================~%"
			     "Expression:~%~a ~%BDD:~%~a ~%BDD-OPT:~%~a ~%~a ~a~%")
		expr
		bdd
		bdd-opt
		(bdd-count-nodes bdd)
		(bdd-count-nodes bdd-opt)))))


(defun ugly-pbt (tester-function num-testcases)
  "Runner for pseudo-PBT tests"
  (dotimes (i num-testcases) (funcall tester-function)))
