(load "utils.lisp")

(typed hashmap-from-list list list hash-table)
(defun hashmap-from-list (varids values)
  "'(1 3 5)  '(0 1 0)   ==>   HashMap{1:0, 3:1, 5:0}" 
  (let ((hm (make-hash-table)))
    (loop for x in varids
	  for y in values do
	    (setf (gethash x hm) (= y 1)))
    hm))

(defun hashmap-quick (l)
  (reduce (lambda (hm xs)
	    (destructuring-bind (L R) xs
	      (hashmap-add L R hm)))
	  l
	  :initial-value (make-hash-table)))
  
(defun add-to-hashmap (k v hashmap) ; deprecated
  (setf (gethash k hashmap) v)
  hashmap)
(defun hashmap-add (k v hashmap)
  (add-to-hashmap k v hashmap))

(defun hashmap-contains (k hashmap)
  (nth-value 1 (gethash k hashmap)))


(defun value-of (varid hashmap)    ; deprecated
  "Given a hashmap, returns hashmap[varid]"
  (nth-value 0 (gethash varid hashmap)))
(defun hashmap-get (varid hashmap)
  "Given a hashmap, returns hashmap[varid]"
  (value-of varid hashmap))

(defun hashmap-keys (hashmap)
  (loop for key being the hash-keys of hashmap
	collect key))


(typed print-hashmap hash-table string)
(defun print-hashmap (hashmap)
  "Returns a string containing the partial representation of a
hash map (no 'NIL values)"
  (apply #'concatenate 'string
	 (loop for value being the hash-values of hashmap
		 using (hash-key key)
               collect (format 'nil "(~A:~A) " key value))))


(defun left-pad (l max-len)
  (if (< (length l) max-len)
      (concatenate 'list
	      (loop for i from 0 below (- max-len (length l))
		   collect 0)
	      l)
      l))


(defun integer-to-bit-list (number num-bits)
  "Convert a number to a list containing its bits.
 ex. 10 => '(1 0 1 0)"
  (left-pad
   (reverse (loop for i from 0 below (integer-length number)
		  collect
		  (logand 1 (ash number (- i)))))
   num-bits))


(typed assignments list list)
(defun assignments (varids)
  "Return bitlist representation of numbers between 0 and |varids|"
  (loop for n in (range (expt 2 (length varids)))
	collect (hashmap-from-list varids (integer-to-bit-list n (length varids)))))


;; ==============================================

(defstruct diyset
  hashmap
  keys
  )

(defun make-set ()
  (make-diyset :hashmap (make-hash-table) :keys '()))

(defun set-contains (set x)
  (hashmap-contains x (diyset-hashmap set)))

(defun set-add (set x)
  (if (set-contains set x) set
      (make-diyset
        :hashmap (add-to-hashmap x 't (diyset-hashmap set))
        :keys    (cons x (diyset-keys set)))))


(set-add (set-add (make-set) 'lol) 123)
