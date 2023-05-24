(defmacro typed (nomefunc &rest types)
  "Alternative syntax for function types declaration"
  `(declaim
    (ftype
     (function ,(butlast types) ,(car (last types)))
     ,nomefunc)))


(defun range (max &key (min 0) (step 1))
   (loop for n from min below max by step
	 collect n))

