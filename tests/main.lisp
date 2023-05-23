(defpackage theorem-prover/tests/main
  (:use :cl
        :theorem-prover
        :rove))
(in-package :theorem-prover/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :theorem-prover)' in your Lisp.

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))
