(ns latte-sets.equiv
  "Equivalence relations"

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte 
             :refer [definition defthm defaxiom defnotation
                     forall lambda
                     assume have pose proof qed lambda]]

            [latte-prelude.prop :as p
             :refer [and and* not]]

            [latte-prelude.equal :as eq
             :refer [equal]]

            [latte-sets.set :as s
             :refer [set elem emptyset set-equal subset seteq]]

            [latte-sets.algebra :as alg
             :refer [inter]]

            [latte-sets.rel :as rel
             :refer [rel reflexive symmetric transitive]]

            [latte-sets.quant :as sq
             :refer [forall-in]]

            [latte-sets.powerset :as pset
             :refer [powerset set-ex set-elem]]

            [latte-sets.powerrel :as prel
             :refer [powerrel]]

            ))

;;;; =============== EQUIVALENCE RELATIONS ==============

(definition equivalence
  "An equivalence relation."
  [?T :type, R (rel T T)]
  (and* (reflexive R)
        (symmetric R)
        (transitive R)))

(defthm ident-equiv
  "The indentity on `T` is an equivalence relation."
  [T :type]
  (equivalence (rel/identity T)))

(proof 'ident-equiv
  (qed (p/and-intro* (rel/ident-refl T)
                     (rel/ident-sym T)
                     (rel/ident-trans T))))


(defthm equiv-refl
  [?T :type, R (rel T T), eqR (equivalence R)]
  (reflexive R))

(proof 'equiv-refl-thm
  (qed (p/and-elim* 1 eqR)))

(defthm equiv-sym
  [?T :type, R (rel T T), eqR (equivalence R)]
  (symmetric R))

(proof 'equiv-sym-thm
  (qed (p/and-elim* 2 eqR)))

(defthm equiv-trans
  [?T :type, R (rel T T), eqR (equivalence R)]
  (transitive R))

(proof 'equiv-trans-thm
  (qed (p/and-elim* 3 eqR)))

(definition eqclass
  "The equivalence class of element `x` wrt. relation `R`."
  [?T :type, x T, R (rel T T), eqR (equivalence R)]
  (lambda [y T]
    (R x y)))


(defthm eqclass-mem
  [?T :type, x T, R (rel T T), eqR (equivalence R)]
  (elem x (eqclass x R eqR)))

(proof 'eqclass-mem-thm
  (have <a> (R x x) :by ((p/and-elim* 1 eqR) x))
  (qed <a>))


(defthm eqclass-subset
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (R x y)
       (subset (eqclass x R eqR)
               (eqclass y R eqR))))

(proof 'eqclass-subset-thm
  (assume [HR (R x y)
           z T
           Hz (elem z (eqclass x R eqR))]
    (have <a> (R x z) :by Hz)
    (have <b> (R y x) :by ((equiv-sym R eqR) x y HR))
    (have <c> (R y z) :by ((equiv-trans R eqR) y x z <b> <a>)))
  (qed <c>))

(defthm eqclass-eq
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (R x y)
       (seteq (eqclass x R eqR)
              (eqclass y R eqR))))

(proof 'eqclass-eq-thm
  (assume [HR (R x y)]
    (have <a> (subset (eqclass x R eqR)
                      (eqclass y R eqR)) 
          :by ((eqclass-subset x y R eqR) HR))
    (have <b1> (R y x) :by ((equiv-sym R eqR) x y HR))
    (have <b> (subset (eqclass y R eqR)
                      (eqclass x R eqR))
          :by ((eqclass-subset y x R eqR) <b1>))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm eqclass-equal
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (R x y)
       (set-equal (eqclass x R eqR) 
                  (eqclass y R eqR))))

(proof 'eqclass-equal-thm
  (assume [HR (R x y)]
    (have <a> _ :by ((s/seteq-implies-set-equal (eqclass x R eqR)
                                                (eqclass y R eqR))
                     ((eqclass-eq x y R eqR) HR))))
  (qed <a>))

;;;; ==================== PARTITIONS ==================

(definition all-nonempty
  [?T :type, P (powerset T)]
  (forall [s (set T)]
    (==> (set-elem s P)
         (s/non-empty s))))

(definition partition-member
  "The elements of set `s` are members of partition `P`"
  [?T :type, s (set T), P (powerset T)]
  (forall-in [x s]
    (set-ex (lambda [sp (set T)]
              (and (set-elem sp P)
                   (elem x sp))))))

(definition all-disjoint
  "The sets of partition `P` are all disjoints"
  [?T :type, P (powerset T)]
  (forall [s1 s2 (set T)]
    (==> (set-elem s1 P)
         (set-elem s2 P)
         (not (set-equal s1 s2))
         (alg/disjoint s1 s2))))

(definition partition
  "`P` is a partition of set `s`"
  [?T :type, s (set T), P (powerset T)]
  (and* (all-nonempty P)
        (partition-member s P)
        (all-disjoint P)))











