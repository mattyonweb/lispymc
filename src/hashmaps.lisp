(load "utils.lisp")

(typed hashmap-from-list list list hash-table)
(defun hashmap-from-list (varids values)
  "'(1 3 5)  '(0 1 0)   ==>   HashMap{1:0, 3:1, 5:0}" 
  (let ((hm (make-hash-table)))
    (loop for x in varids
	  for y in values do
	    (setf (gethash x hm) (= y 1)))
    hm))

(defun add-to-hashmap (k v hashmap)
  (setf (gethash k hashmap) v))

(typed value-of integer hash-table t)
(defun value-of (varid hashmap)
  "Given a hashmap, returns hashmap[varid]"
  (nth-value 0 (gethash varid hashmap)))


(typed print-hashmap hash-table string)
(defun print-hashmap (hashmap)
  "Returns a string containing the partial representation of a
hash map (no 'NIL values)"
  (apply #'concatenate 'string
	 (loop for value being the hash-values of hashmap
		 using (hash-key key)
               collect (format 'nil "(~A:~A) " key value))))


(typed integer-to-bit-list integer list)
(defun integer-to-bit-list (number)
  "Convert a number to a list containing its bits.
 ex. 10 => '(1 0 1 0)"
  (reverse (loop for i from 0 below (integer-length number)
		 collect (logand 1 (ash number (- i))))))



(typed assignments list list)
(defun assignments (varids)
  "Return bitlist representation of numbers between 0 and |varids|"
  (loop for n in (range (expt 2 (length varids)))
	collect (hashmap-from-list varids (integer-to-bit-list n))))

