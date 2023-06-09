(defsystem "theorem-prover"
  :version "0.1.0"
  :author ""
  :license ""
  :depends-on ()
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description ""
  :in-order-to ((test-op (test-op "theorem-prover/tests"))))

(defsystem "theorem-prover/tests"
  :author ""
  :license ""
  :depends-on ("theorem-prover"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for theorem-prover"
  :perform (test-op (op c) (symbol-call :rove :run c)))
