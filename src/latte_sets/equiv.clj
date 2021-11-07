(ns latte-sets.equiv
  "Equivalence relations, quotients, etc."

  (:refer-clojure :exclude [and or not set partition])

  (:require [latte.core :as latte 
             :refer [definition defthm deflemma defaxiom defnotation
                     forall lambda
                     assume have pose proof try-proof qed lambda]]

            [latte-prelude.prop :as p
             :refer [and and* or not]]

            [latte-prelude.equal :as eq
             :refer [equal]]

            [latte-prelude.quant :as q
             :refer [exists]]

            [latte-prelude.classic :as classic]

            [latte-sets.set :as s
             :refer [set elem emptyset set-equal subset seteq]]

            [latte-sets.algebra :as alg
             :refer [inter]]

            [latte-sets.rel :as rel
             :refer [rel reflexive symmetric transitive]]

            [latte-sets.quant :as sq
             :refer [forall-in exists-in]]

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

(defthm eqclass-non-empty
  [?T :type, x T, R (rel T T), eqR (equivalence R)]
  (s/non-empty (eqclass x R eqR)))

(proof 'eqclass-non-empty-thm
  (qed ((s/non-empty-elem x (eqclass x R eqR))
        (eqclass-mem x R eqR))))
                          
(defthm eqclass-rel
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (elem y (eqclass x R eqR))
       (R x y)))

(proof 'eqclass-rel-thm
  (assume [H (elem y (eqclass x R eqR))]
    (have <a> (R x y) :by H))
  (qed <a>))


(defthm eqclass-rel-conv
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (R x y)
       (elem y (eqclass x R eqR))))

(proof 'eqclass-rel-conv-thm
  (assume [H (R x y)]
    (have <a> _ :by H))
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


(defthm eqclass-not-elem
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (not (R x y))
       (not (elem y (eqclass x R eqR)))))

(proof 'eqclass-not-elem-thm
  (assume [Hxy (not (R x y))]
    (assume [Hcontra (elem y (eqclass x R eqR))]
      (have <a>  (R x y) :by ((eqclass-rel x y R eqR) Hcontra))
      (have <b> p/absurd :by (Hxy <a>))))
  (qed <b>))

(defthm eqclass-not-subset
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (not (R x y))
       (not (subset (eqclass y R eqR) (eqclass x R eqR)))))

(proof 'eqclass-not-subset-thm
  (assume [Hxy (not (R x y))]
    (assume [Hcontra (subset (eqclass y R eqR) (eqclass x R eqR))]
      (have <a> (elem y (eqclass y R eqR)) :by (eqclass-mem y R eqR))
      (have <b> (elem y (eqclass x R eqR)) 
            :by ((s/subset-elim (eqclass y R eqR) (eqclass x R eqR) y)
                 <a> Hcontra))
      (have <c> (R x y) :by ((eqclass-rel x y R eqR) <b>))
      (have <d> p/absurd :by (Hxy <c>))))
  (qed <d>))
 
(defthm eqclass-not-seteq
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (not (R x y))
       (not (seteq (eqclass x R eqR) (eqclass y R eqR)))))

(proof 'eqclass-not-seteq-thm
  (assume [Hxy (not (R x y))]
    (have <a> (not (subset (eqclass y R eqR) (eqclass x R eqR)))
          :by ((eqclass-not-subset x y R eqR) Hxy))
    (assume [Hcontra (seteq (eqclass x R eqR) (eqclass y R eqR))]
      (have <b> (subset (eqclass y R eqR) (eqclass x R eqR))
            :by (p/and-elim-right Hcontra))
      (have <c> p/absurd :by (((eqclass-not-subset x y R eqR) Hxy) <b>))))
  (qed <c>))

(defthm eqclass-disjoint
  [[?T :type] [x y T] [R (rel T T)] [eqR (equivalence R)]]
  (==> (not (R x y))
       (alg/disjoint (eqclass x R eqR) (eqclass y R eqR))))

(proof 'eqclass-disjoint-thm
  (assume [Hxy (not (R x y))]
    "We want to show that the intersection of the twoclasses is a subset of the emptyset"
    (assume [z T
             Hz (elem z (inter (eqclass x R eqR) (eqclass y R eqR)))]
      (have <a1> (elem z (eqclass x R eqR)) :by (p/and-elim-left Hz))
      (have <a> (R x z) :by ((eqclass-rel x z R eqR) <a1>))
      (have <b1> (elem z (eqclass y R eqR)) :by (p/and-elim-right Hz))
      (have <b> (R y z) :by ((eqclass-rel y z R eqR) <b1>))
      (have <c> (R z y) :by ((equiv-sym R eqR) y z <b>))
      (have <d> (R x y) :by (((equiv-trans R eqR) x z y) <a> <c>))
      (have <e> p/absurd :by (Hxy <d>))
      (have <f> (elem z (emptyset T)) :by (<e> (elem z (emptyset T)))))
    (have <g> (subset (inter (eqclass x R eqR) (eqclass y R eqR)) (emptyset T)) 
          :by <f>)
    (have <h> (subset (emptyset T) (inter (eqclass x R eqR) (eqclass y R eqR)))
          :by (s/subset-emptyset-lower-bound (inter (eqclass x R eqR) (eqclass y R eqR))))
    (have <i> (seteq (inter (eqclass x R eqR) (eqclass y R eqR)) (emptyset T))
          :by (p/and-intro <g> <h>))
    (have <j> (set-equal (inter (eqclass x R eqR) (eqclass y R eqR)) (emptyset T))
          :by ((s/seteq-implies-set-equal (inter (eqclass x R eqR) (eqclass y R eqR)) (emptyset T)) <i>)))
  (qed <j>))

(definition quotient
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (lambda [eqx (set T)]
    (exists-in [x s]
      (and (elem x eqx)
           (set-equal eqx (eqclass x R eqR))))))

(defthm quotient-eqclass
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (forall-in [x s]
    (set-elem (eqclass x R eqR) (quotient s R eqR))))

(proof 'quotient-eqclass-thm
  (assume [x T
           Hx (elem x s)]
    (pose P := (lambda [y T]
                 (and (elem y s)
                      (and (elem y (eqclass x R eqR))
                           (set-equal (eqclass x R eqR) (eqclass y R eqR))))))
    (have <a> (elem x (eqclass x R eqR)) :by (eqclass-mem x R eqR))
    (have <b> (set-equal (eqclass x R eqR) (eqclass x R eqR))
          :by (s/set-equal-refl (eqclass x R eqR)))
    (have <c> (P x) :by (p/and-intro Hx (p/and-intro <a> <b>)))
    (have <d> (q/ex P) :by ((q/ex-intro P x) <c>))
    (have <e> (set-elem (eqclass x R eqR) (quotient s R eqR)) :by <d>))
  (qed <e>))

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

(deflemma quot-part-non-empty
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (all-nonempty (quotient s R eqR)))

(proof 'quot-part-non-empty-lemma
  (assume [xcls (set T)
           Hxcls (set-elem xcls (quotient s R eqR))]
    (have <a> (exists [x T]
                (and (elem x s)
                     (and (elem x xcls)
                          (set-equal xcls (eqclass x R eqR)))))
          :by Hxcls)
    (assume [x T
             Hx (and (elem x s)
                     (and (elem x xcls)
                          (set-equal xcls (eqclass x R eqR))))]
      (have <b> (s/non-empty (eqclass x R eqR))
            :by (eqclass-non-empty x R eqR))
      (have <c> (set-equal xcls (eqclass x R eqR)) :by (p/and-elim-right (p/and-elim-right Hx)))
      
      (have <d> (s/non-empty xcls) 
            :by ((p/and-elim-right (<c> (lambda [$ (set T)] (s/non-empty $)))) <b>)))
    (have <e> (s/non-empty xcls) :by (q/ex-elim <a> <d>)))
  (qed <e>))


(deflemma quot-part-members
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (partition-member s (quotient s R eqR)))

(proof 'quot-part-members-lemma
  (assume [x T
           Hx (elem x s)]
    (pose P := (lambda [sp (set T)] (and (set-elem sp (quotient s R eqR))
                                         (elem x sp))))
    (have <a> (set-elem (eqclass x R eqR) (quotient s R eqR))
          :by ((quotient-eqclass s R eqR) x Hx))
    (have <b> (elem x (eqclass x R eqR)) :by (eqclass-mem x R eqR))
    (have <c> (P (eqclass x R eqR)) :by (p/and-intro <a> <b>))
    (have <d> (set-elem (eqclass x R eqR) P) :by <c>)
    (have <e> (set-ex (lambda [sp (set T)] (and (set-elem sp (quotient s R eqR))
                                                (elem x sp)))) 
          :by ((pset/set-ex-intro P (eqclass x R eqR)) <d>)))
  (qed <e>))

(deflemma quot-part-disjoints
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (all-disjoint (quotient s R eqR)))

(proof 'quot-part-disjoints-lemma
  (assume [eqx (set T) 
           eqy (set T)
           Heqx (set-elem eqx (quotient s R eqR))
           Heqy (set-elem eqy (quotient s R eqR))
           Hneq (not (set-equal eqx eqy))]
    (assume [x T
             Hx (and (elem x s)
                     (and (elem x eqx)
                          (set-equal eqx (eqclass x R eqR))))]
      (assume [y T
               Hy (and (elem y s)
                       (and (elem y eqy)
                            (set-equal eqy (eqclass y R eqR))))]
        "We use a classical reasoning (is this provable intuitionistically ?)"
        (assume [HRyes (R x y)]
          (have <a1> (set-equal (eqclass x R eqR) (eqclass y R eqR))
                :by ((eqclass-equal x y R eqR) HRyes))
          (have <a2> (set-equal eqx (eqclass y R eqR))
                :by ((s/set-equal-trans eqx (eqclass x R eqR) (eqclass y R eqR))
                     (p/and-elim-right (p/and-elim-right Hx)) <a1>))
          (have <a3> (set-equal eqx eqy)
                :by ((s/set-equal-trans eqx (eqclass y R eqR) eqy)
                     <a2> ((s/set-equal-sym eqy (eqclass y R eqR))
                           (p/and-elim-right (p/and-elim-right Hy)))))
          (have <a4> p/absurd :by (Hneq <a3>))
          (have <a> (alg/disjoint eqx eqy) :by (<a4> (alg/disjoint eqx eqy))))
        (assume [HRno (not (R x y))]
          (have <b1> (alg/disjoint (eqclass x R eqR) (eqclass y R eqR))
                :by ((eqclass-disjoint x y R eqR) HRno))
          (have <b2> (alg/disjoint eqx (eqclass y R eqR))
                :by ((s/set-equal-subst-prop 
                      (lambda [$ (set T)] (alg/disjoint $ (eqclass y R eqR)))
                      (eqclass x R eqR) eqx)
                     ((s/set-equal-sym eqx (eqclass x R eqR)) (p/and-elim-right (p/and-elim-right Hx)))
                     <b1>))
          (have <b> (alg/disjoint eqx eqy)
                :by ((s/set-equal-subst-prop
                      (lambda [$ (set T)] (alg/disjoint eqx $))
                      (eqclass y R eqR) eqy)
                     ((s/set-equal-sym eqy (eqclass y R eqR)) (p/and-elim-right (p/and-elim-right Hy)))
                     <b2>)))
        (have <c> (or (R x y) (not (R x y)))
              :by (classic/excluded-middle-ax (R x y)))
        (have <d> (alg/disjoint eqx eqy) :by (p/or-elim <c> <a> <b>)))
      (have <e> (alg/disjoint eqx eqy) :by (q/ex-elim Heqy <d>)))
    (have <f> (alg/disjoint eqx eqy) :by (q/ex-elim Heqx <e>)))
  (qed <f>))

(defthm quotient-partition
  "The quotient of set `s` wrt. equivalence relation `R`
is a partition of `s`"
  [?T :type, s (set T), R (rel T T), eqR (equivalence R)]
  (partition s (quotient s R eqR)))

(proof 'quotient-partition-thm
  (qed (p/and-intro* (quot-part-non-empty s R eqR)
                     (quot-part-members s R eqR)
                     (quot-part-disjoints s R eqR))))


