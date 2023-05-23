(load "bdd.lisp")

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
    ; iterate on all possible assignments for the varids
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



(defun tester-compare-bdd-unique-vars ()
  "Test whether the eval of a random bexpr and relative BDD are equal"
  (let*
      ((expr (random-expr 1))
       (bdd  (bdd-generate expr))  
       (eval-on-expr (unique-vars expr))
       (eval-on-bdd  (bdd-unique-vars bdd)))
    (if (not (equal eval-on-expr eval-on-bdd))
	(format t
		(concatenate 'string
			     "~%=========================~%"
			     "Expression:~%~a ~%BDD:~%~a ~%~a ~a~%")
		expr
		bdd
		eval-on-expr
		eval-on-bdd))))


(defun tester-compare-bdd-and ()
  "Test whether the eval of a random bexpr and relative BDD are equal"
  (let*
      ((expr1 (random-expr 1))
       (expr2 (random-expr 1))
       (expr3 (list 'and expr1 expr2))
       (bdd1  (bdd-generate expr1))    
       (bdd2  (bdd-generate expr2))    
       (bdd3  (bdd-and bdd1 bdd2 #'min)))    
    ; iterate on all possible assignments for the varids
    (loop for hashmap in (assignments (unique-vars expr3)) do
      (let
	  ((eval-on-expr (eval-expr-assignment expr3 hashmap))
	   (eval-on-bdd  (bdd-eval bdd3 hashmap)))
	(if (not (eq eval-on-expr eval-on-bdd))
	    (format t
		    (concatenate 'string
		     "~%=========================~%"
		     "Expression:~%~a ~%BDD:~%~a ~%Assignment:~%~a ~%~a ~a~%")
		    expr3
		    bdd3
		    (print-hashmap hashmap)
		    eval-on-expr
		    eval-on-bdd))))))

;; ======================================================

(defun ugly-pbt (tester-function num-testcases)
  "Runner for pseudo-PBT tests"
  (dotimes (i num-testcases) (funcall tester-function)))

(ugly-pbt #'tester-compare-bdd-expr 1000)
(ugly-pbt #'tester-compare-bdd-unique-vars 1000)
(ugly-pbt #'tester-optimized-bdd-has-less-nodes 1000)
(ugly-pbt #'tester-compare-bdd-and 1000)
(print "tests: ok")