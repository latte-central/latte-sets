(ns latte-sets.compare

  "Comparing sets"
  
  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm try-defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof try-proof qed lambda]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and and* or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-sets.set :as set :refer [set]]
            
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.ralgebra :as ra]

            [latte-sets.powerrel :as prel :refer [rel-ex]]

            [latte-sets.pfun :as pfun :refer [injection bijection pfcomp-mid]]

            ))


;;; XXX : are functionality and seriality required in the definition ?
(definition smaller
  "The set `s1` is \"smaller\" than `s2`."
  [[?T ?U :type] [s1 (set T)] [s2 (set U)]]
  (rel-ex (lambda [f (rel T U)]
            (injection f s1 s2))))


(definition equipotent
  "The set `s1` has the same \"size\" as `s2`."
  [[?T ?U :type] [s1 (set T)] [s2 (set U)]]
  (rel-ex (lambda [f (rel T U)]
            (bijection f s1 s2))))

(defthm equipotent-refl
  [[?T :type] [s (set T)]]
  (equipotent s s))

(proof 'equipotent-refl-thm
  (have <a> (bijection (rel/identity T) s s)
        :by (pfun/ridentity-bijection s))
  (qed ((prel/rel-ex-intro (lambda [f (rel T T)]
                             (bijection f s s)) (rel/identity T))
        <a>)))

(defthm equipotent-sym
  [[?T ?U :type] [s1 (set T)] [s2 (set U)]]
  (==> (equipotent s1 s2)
       (equipotent s2 s1)))

(proof 'equipotent-sym-thm
  (assume [Heq (equipotent s1 s2)]

    (assume [f (rel T U)
             Hf (bijection f s1 s2)]
      "We have to find a bijection from s2 to s1
.. which is of course the (relational) inverse."

      (have <a> (bijection (ra/rinverse f) s2 s1)
            :by (pfun/bijection-inverse-bijection f s1 s2 Hf))

      (have <b> (equipotent s2 s1)
            :by ((prel/rel-ex-intro (lambda [g (rel U T)]
                                      (bijection g s2 s1)) (ra/rinverse f))
                 <a>)))


    (have <c> _ :by ((prel/rel-ex-elim (lambda [f (rel T U)]
                                         (bijection f s1 s2))
                                       (equipotent s2 s1))
                     Heq <b>)))

  (qed <c>))

(defthm equipotent-trans
  [[?T ?U ?V :type] [s1 (set T)] [s2 (set U)] [s3 (set V)]]
  (==> (equipotent s1 s2)
       (equipotent s2 s3)
       (equipotent s1 s3)))

(proof 'equipotent-trans-thm
  (assume [Heq1 _ 
           Heq2 _]
    
    (assume [g (rel U V)
             Hg (bijection g s2 s3)]

      (assume [f (rel T U)
               Hf (bijection f s1 s2)]

        (have <a> (bijection (pfcomp-mid f g s1 s2 s3) s1 s3)
              :by ((pfun/pfcomp-bijection-mid f g s1 s2 s3)
                   Hf Hg))

        (have <b> _
              :by ((prel/rel-ex-intro (lambda [h (rel T V)]
                                        (bijection h s1 s3))
                                      (pfcomp-mid f g s1 s2 s3)) <a>)))

      (have <c> _ :by ((prel/rel-ex-elim (lambda [f (rel T U)]
                                           (bijection f s1 s2))
                                         (equipotent s1 s3))
                       Heq1 <b>)))

    (have <d> _ :by ((prel/rel-ex-elim (lambda [g (rel U V)]
                                           (bijection g s2 s3))
                                         (equipotent s1 s3))
                       Heq2 <c>)))

  (qed <d>))
