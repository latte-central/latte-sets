(ns latte-sets.powerrel

  "Notions about the relational powerset construction.

  This is akin to [[latte-sets.powerset]] but for relations."

    (:refer-clojure :exclude [and or not set])

    (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                            forall lambda
                                            assume have pose proof qed lambda]]
              [latte.utils :as u]
              [latte-prelude.quant :as q :refer [exists]]
              [latte-prelude.prop :as p :refer [<=> and or not]]
              [latte-prelude.equal :as eq :refer [equal]]

              [latte-sets.set :as s :refer [set elem seteq subset]]
              
              [latte-sets.rel :as r :refer [rel subrel releq transitive]]
              [latte-sets.powerset :as powerset :refer [powerset set-ex]]))

(definition powerrel
  "The powerset constructor for relations.

The term `(powerrel T U)' is the type
of sets whose elements are relations of type `(rel T U)`."
  [[T U :type]]
  (==> (rel T U) :type))

(definition rel-elem
  "Membership for powersets.
Th relation `R` is an element of the set `X`."
  [[?T ?U :type] [R (rel T U)] [X (powerrel T U)]]
  (X R))

(defn fetch-powerrel-types [def-env ctx r-type]
  "Fetch the `T` and `U`  in a powerrel-type `s-type` of the form `(powerrel T U)` (fails otherwise).
This function is used for implicit in relations."
  (let [[RT _] (p/decompose-impl-type def-env ctx r-type)]
    (r/fetch-rel-type def-env ctx RT)))

;; implicit type parameters for power-relations
(u/register-implicit-type-parameters-handler! 'powerrel fetch-powerrel-types 2)

(definition rel-ex
  "The powerset existential for relations.

There exists an element relation `R` of the powerset `X` such that...

This is the definition of [[latte.quant/ex]] but
adpated for relations."
  [[?T ?U :type] [X (powerrel T U)]]
  (forall [α :type]
    (==> (forall [R (rel T U)]
           (==> (rel-elem R X) α))
         α)))

(defthm rel-ex-elim
  "The elimination rule for the relation existential."
  [[?T ?U :type] [X (powerrel T U)] [A :type]]
  (==> (rel-ex X)
       (forall [R (rel T U)]
         (==> (rel-elem R X) A))
       A))

(proof 'rel-ex-elim-thm
  (assume [H1 (rel-ex X)
           H2 (forall [R (rel T U)] (==> (rel-elem R X) A))]
    (have <a> (==> (forall [R (rel T U)]
                           (==> (rel-elem R X) A))
                   A) :by (H1 A))
    (have <b> A :by (<a> H2)))
  (qed <b>))

(defthm rel-ex-intro
  "Introduction rule for [[rel-ex]]."
  [[?T ?U :type] [X (powerrel T U)] [R (rel T U)]]
  (==> (rel-elem R X)
       (rel-ex X)))

(proof 'rel-ex-intro-thm
  (assume [H (rel-elem R X)
           A :type
           Q (forall [S (rel T U)] (==> (rel-elem S X) A))]
    (have <a> (==> (rel-elem R X) A) :by (Q R))
    (have <b> A :by (<a> H)))
  (qed <b>))

(definition rel-single
  "The relational powerset version of [[latte-prelude.quant/single]].
 There is a single relation element in `X` such that..."
  [[?T ?U :type] [X (powerrel T U)]]
  (forall [R S (rel T U)]
    (==> (rel-elem R X)
         (rel-elem S X)
         (releq R S))))

(definition rel-unique
  "The relational powerset version of [[latte-prelude.quant/unique]].
There exists a unique relation R in the set of relations X such that ..."
  [[?T ?U :type] [X (powerrel T U)]]
  (and (rel-ex X)
       (rel-single X)))

(defaxiom the-rel
  "The relation powerset version of [[latte-prelude.quant/the]]."
  [[?T ?U :type] [X (powerrel T U)] [u (rel-unique X)]]
  (rel T U))

(defaxiom the-rel-prop
  "The property of the unique set descriptor [[the-rel]]."
  [[?T ?U :type] [X (powerrel T U)] [u (rel-unique X)]]
  (rel-elem (the-rel X u) X))

(defthm the-rel-lemma
  "The unique relation ... is unique."
  [[?T ?U :type] [X (powerrel T U)] [u (rel-unique X)]]
  (forall [R (rel T U)]
    (==> (rel-elem R X)
         (releq R (the-rel X u)))))

(proof 'the-rel-lemma-thm
  (have <a> (rel-single X) :by (p/and-elim-right u))
  (have <b> (rel-elem (the-rel X u) X) :by (the-rel-prop X u))
  (assume [R (rel T U)
           HR (rel-elem R X)]
    (have <c> (==> (rel-elem R X)
                   (rel-elem (the-rel X u) X)
                   (releq R (the-rel X u))) :by (<a> R (the-rel X u)))
    (have <d> (releq R (the-rel X u)) :by (<c> HR <b>)))
  (qed <d>))


(definition runions
  "Generalized relation union."
  [[?T ?U :type] [RR (powerrel T U)]]
  (lambda [x T]
    (lambda [y U]
      (rel-ex (lambda [R (rel T U)]
                (and (rel-elem R RR)
                     (R x y)))))))

(defthm runions-upper-bound
   "The generalized relational union is an upper bound wrt. 
the [[subrel]] relation."
   [[?T ?U :type] [RR (powerrel T U)]]
   (forall [R (rel T U)]
     (==>  (rel-elem R RR)
           (subrel R (runions RR)))))

(proof 'runions-upper-bound-thm
  (assume [R (rel T U)
           HR (rel-elem R RR)]
    (assume [x T y U
             Hxy (R x y)]
      (pose U := (lambda [S (rel T U)]
                   (and (rel-elem S RR)
                        (S x y))))
      (have <a> (rel-elem R U) :by (p/and-intro HR Hxy))
      (have <b> ((runions RR) x y) :by ((rel-ex-intro U R) <a>))))
  (qed <b>))


(definition rintersections
  "Generalized relational intersection."
  [[?T ?U :type] [RR (powerrel T U)]]
  (lambda [x T]
    (lambda [y U]
      (forall [R (rel T U)]
      (==> (rel-elem R RR)
           (R x y))))))

(defthm rintersections-lower-bound
  "The generalized intersection is a lower bound wrt. the [[subrel]] relation."
  [[?T ?U :type] [RR (powerrel T U)]]
  (forall [R (rel T U)]
    (==> (rel-elem R RR)
         (subrel (rintersections RR) R))))

(proof 'rintersections-lower-bound-thm
  (assume [R (rel T U)
           Hx (rel-elem R RR)]
    (assume [x T y U
             Hxy ((rintersections RR) x y)]
      (have <a> (R x y) :by (Hxy R Hx))))
  (qed <a>))

(defthm rintersections-prop
  "Preservation of properties on relational intersections."
  [[?T ?U :type] [P (==> T U :type)] [RR (powerrel T U)]]
  (forall [R (rel T U)]
    (==> (rel-elem R RR)
         (forall [x T]
           (forall [y U]
             (==> (R x y)
                  (P x y))))
         (forall [x T]
           (forall [y U]
             (==> ((rintersections RR) x y)
                  (P x y)))))))

(proof 'rintersections-prop-thm
  (assume [R (rel T U)
           H1 (rel-elem R RR)
           H2 (forall [x T]
                (forall [y U]
                  (==> (R x y)
                       (P x y))))]
    (assume [x T y U
             Hxy ((rintersections RR) x y)]
      (have <a> (==> (R x y)
                     (P x y)) :by (H2 x y))
      (have <b> (R x y)
            :by ((rintersections-lower-bound RR) R H1 x y Hxy))
      (have <c> (P x y) :by (<a> <b>))))
  (qed <c>))

(definition trans-closure-set
  "The set of transitively-closed relation."
  [?T :type, R (rel T T)]
  (lambda [S (rel T T)]
    (and (subrel R S)
         (transitive S))))

(definition trans-closure
  "The transitive closure of `R`, cf. [[rel/transitive]]
*Remark*: it is defined in the [[powerrel]] namespace
because the definition requires [[rintersections]]."
  [?T :type, R (rel T T)]
  (rintersections (trans-closure-set R)))

(defthm transitive-trans-closure
  [?T :type, R (rel T T)]
  (transitive (trans-closure R)))

(proof 'transitive-trans-closure-thm
  (pose R+ := (trans-closure R))
  (assume [x T y T z T
           Hxy (R+ x y) Hyz (R+ y z)]
    (assume [S (rel T T)
             HS (rel-elem S (trans-closure-set R))]
      (have <a> (subrel R+ S) :by ((rintersections-lower-bound (trans-closure-set R)) S HS))
      (have <b> (S x y) :by (<a> x y Hxy))
      (have <c> (S y z) :by (<a> y z Hyz))
      (have <d> (transitive S) :by (p/and-elim-right HS))
      (have <e> (S x z) :by (<d> x y z <b> <c>)))
    (have <f> (R+ x z) :by <e>))
  (qed <f>))
  
(defthm trans-closure-sub
  [?T :type, R (rel T T)]
  (subrel R (trans-closure R)))

(proof 'trans-closure-sub-thm
  (pose R+ := (rintersections (lambda [S (rel T T)]
                                (and (subrel R S)
                                     (transitive S)))))
  (assume [x T y T
           Hxy (R x y)]
    (assume [S (rel T T)
             HS (and (subrel R S)
                     (transitive S))]
      (have <a> (S x y) :by ((p/and-elim-left HS) x y Hxy)))
    (have <b> (R+ x y) :by <a>))
  (qed <a>))

(defthm trans-closure-smallest
  [?T :type, R (rel T T)]
  (forall [S (rel T T)]
    (==> (subrel R S)
         (transitive S)
         (subrel (trans-closure R) S))))

(proof 'trans-closure-smallest-thm
  (assume [S _ Hsub _ Htrans _]
    (assume [x T y T
             Hxy ((trans-closure R) x y)]
      (have <a> (rel-elem S (trans-closure-set R))
            :by (p/and-intro Hsub Htrans))
      (have <b> (S x y) :by (Hxy S <a>))))
  (qed <b>))

(comment

(definition full-powerset
  "The powerset containing all the subsets of type `T`."
  [[T :type]]
  (lambda [x (set T)]
    p/truth))

(defthm full-powerset-prop
  [[T :type]]
  (forall [x (set T)]
    (set-elem x (full-powerset T))))

(proof 'full-powerset-prop
  (assume [x (set T)]
    (have <a> ((full-powerset T) x) :by p/truth-is-true))
  (qed <a>))

(definition empty-powerset
  "The empty powerset."
  [[T :type]]
  (lambda [x (set T)]
    p/absurd))

(defthm empty-powerset-prop
  [[T :type]]
  (forall [x (set T)]
    (not (set-elem x (empty-powerset T)))))

(proof 'empty-powerset-prop
  (assume [x (set T)
           H (set-elem x (empty-powerset T))]
    (have <a> p/absurd :by H))
  (qed <a>))

(definition powerset1
  "The powerset of all the non-empty subsets of type `T`."
  [[T :type]]
  (lambda [x (set T)]
    (not (s/set-equal x (s/emptyset T)))))

(defthm powerset1-prop
  [[T :type] [x (set T)]]
  (==> (not (s/set-equal x (s/emptyset T)))
       (set-elem x (powerset1 T))))

(proof 'powerset1-prop
  (assume [H (not (s/set-equal x (s/emptyset T)))]
    (have <a> (set-elem x (powerset1 T)) :by H))
  (qed <a>))

(defthm powerset1-prop-conv
  [[T :type] [x (set T)]]
  (==> (set-elem x (powerset1 T))
       (not (s/set-equal x (s/emptyset T)))))

(proof 'powerset1-prop-conv
  (assume [H (set-elem x (powerset1 T))]
    (assume [Heq (s/set-equal x (s/emptyset T))]
      (have <a> (not (s/set-equal x (s/emptyset T)))
            :by H)
      (have <b> p/absurd :by (<a> Heq))))
  (qed <b>))

(defthm powerset1-prop-equiv
  [[T :type] [x (set T)]]
  (<=> (set-elem x (powerset1 T))
       (not (s/set-equal x (s/emptyset T)))))

(proof 'powerset1-prop-equiv
  (qed (p/and-intro (powerset1-prop T x)
                    (powerset1-prop-conv T x))))
)
