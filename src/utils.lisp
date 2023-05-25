(defmacro typed (nomefunc &rest types)
  "Alternative syntax for function types declaration"
  `(declaim
    (ftype
     (function ,(butlast types) ,(car (last types)))
     ,nomefunc)))


(defun memoizer (fn test-function)
  (let ((cache (make-hash-table :test test-function)))
    #'(lambda (&rest args)
        (multiple-value-bind (result exists)
            (gethash args cache)
          (if exists result
	      (let ((call-output (apply fn args)))
		(progn
		  (setf (gethash args cache) call-output) ;;add to hashmap
		  call-output)))))))


(defmacro memoize (func &optional test-func)
  "After a (defun funcname ...), invoke (memoize funcname) to make it memoized"
  (if (null test-func)
      `(setf (fdefinition 'func) (memoizer #',func #'equalp))
      `(setf (fdefinition 'func) (memoizer #',func #',test-func))))


(defun range (max &key (min 0) (step 1))
   (loop for n from min below max by step
	 collect n))

(defun list-max (l) (loop for x in l maximizing x))
(defun list-min (l) (loop for x in l minimizing x))
