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


(typed truth-value? symbol boolean)
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
	  (truthval-of expr hashmap)
	  (not (truthval-of (abs expr) hashmap))))
     ((and (listp expr) (eq (car expr) 'AND))  
      (every #'identity
	     (map 'list #'(lambda (e) (eval-expr-assignment e hashmap)) (cdr expr))))
     ((and (listp expr) (eq (car expr) 'OR))  
      (some #'identity
	    (map 'list #'(lambda (e) (eval-expr-assignment e hashmap)) (cdr expr))))
     (t (error "Can't eval-expr-assignment on ~S" expr))))


;; ======================================================= ;;


(defstruct BDD varid low high)

(defun generate-bdd (expr &optional ordering-function)
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
	 :low   (generate-bdd (expr-sub expr k 'false) ordering-function)
	 :high  (generate-bdd (expr-sub expr k 'true)  ordering-function)))))

(defparameter bdd1 (generate-bdd ex1))


(defun eval-bdd (bdd assignment)
  (if (truth-value? bdd)
      bdd
      (let ((bool (truthval-of (BDD-varid bdd) assignment)))
	(if bool
	    (eval-bdd (BDD-high bdd) assignment)
	    (eval-bdd (BDD-low bdd) assignment)))))

(defun bdd-optimize (bdd hashcache)
  (if (truth-value? bdd) bdd
      (let ((cached-value (gethash bdd hashcache)))
	(if cached-value   ;; if a cached value exists
	    cached-value
	    (make-BDD :varid (BDD-varid bdd)
		      :low   (bdd-optimize (BDD-low bdd)  hashcache)
		      :high  (bdd-optimize (BDD-high bdd) hashcache))))))

(defun bdd)

;; ================ TESTING ========================== ;;

(defun print-hashmap (hashmap)
  (apply #'concatenate 'string
	 (loop for value being the hash-values of hashmap
		 using (hash-key key)
               collect (format 'nil "(~A:~A) " key value))))

(defun integer-to-bit-list (number)
  ;;  10 => '(1 0 1 0)
  (reverse (loop for i from 0 below (integer-length number)
		 collect (logand 1 (ash number (- i))))))

(defun hashmap-from-list (varids values)
  ;; '(1 3 5)  '(0 1 0)   ==>   HashMap{1:0, 3:1, 5:0} 
  (let ((hm (make-hash-table)))
    (loop for x in varids
	  for y in values do
	    (setf (gethash x hm) (= y 1)))
    hm))

(defun assignments (varids)
  (loop for n in (range (expt 2 (length varids)))
	collect (hashmap-from-list varids (integer-to-bit-list n))))

(defun truthval-of (varid hashmap)
  (nth-value 0 (gethash varid hashmap)))


;; (defun tester-bdd-eval1 (expr)
;;   (let
;;       ((bdd (generate-bdd expr)))
;;     (loop for hashmap in (assignments (unique-vars expr)) do
;;       (format t "~a: ~a~%"
;; 	      (print-hashmap hashmap)
;; 	      (eval-bdd bdd hashmap)))))

;; (defun tester-bdd-eval2 (expr func-on-bdd)
;;   (let
;;       ((bdd (func-on-bdd (generate-bdd expr))))
;;     (loop for hashmap in (assignments (unique-vars expr)) do
;;       (format t "~a: ~a~%"
;; 	      (print-hashmap hashmap)
;; 	      (eval-bdd bdd hashmap)))))


(defun bdd-not (bdd)
  (if (truth-value? bdd)
      (not bdd)
      (make-BDD :varid (BDD-varid bdd)
		:low   (bdd-not (BDD-low bdd))
		:high  (bdd-not (BDD-high bdd)))))

(defun bdd-and (bdd1 bdd2)
  
  )
;; ==============================================
;; (defun cat (&rest rest) (concatenate 'string rest))

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
  (let*
      ((expr (random-expr 1))
       (bdd  (generate-bdd expr)))    
    (loop for hashmap in (assignments (unique-vars expr)) do
      (let
	  ((eval-on-expr (eval-expr-assignment expr hashmap))
	   (eval-on-bdd  (eval-bdd bdd hashmap)))
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

(defun ugly-pbt (num-testcases)
  "Generate `num-testcases` expr and compare expr-eval with bdd-eval"
  (dotimes (i num-testcases) (tester-compare-bdd-expr)))

