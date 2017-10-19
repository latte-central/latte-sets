(ns latte-sets.powerset

  "Notions about the powerset construction.

  In the predicate-as-set encoding of set-theoretic notions,
 the powerset construction (i.e. building a set of sets) is
not immediate. The reason is that the set constructor `(set T)'
 is not itself a type (but a kind). Hence we need to replicate
 some part of the type theory (e.g. the existential quantifier)
to deal with powersets."

    (:refer-clojure :exclude [and or not set])

    (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                            defimplicit
                                            forall lambda
                                            assume have pose proof qed lambda]]
              [latte.quant :as q :refer [exists]]
              [latte.prop :as p :refer [<=> and or not]]
              [latte.equal :as eq :refer [equal]]

              [latte-sets.core :as s :refer [set elem seteq subset]]))

(definition powerset
  "The powerset constructor.

The term `(powerset T)' is the type
of sets whose elements are sets of type `T`."
  [[T :type]]
  (==> (set T) :type))

(definition set-elem-def
  "Membership for powersets.
Th set `x` is an element of the powerset `X`."
  [[T :type] [x (set T)] [X (powerset T)]]
  (X x))

(defn fetch-powerset-type [def-env ctx s-type]
  "Fetch the `T` in a powerset-type `s-type` of the form `(powerset T)` (fails otherwise).
This function is used for implicit in sets."
  (let [[ST _] (p/decompose-impl-type def-env ctx s-type)
        T (s/fetch-set-type def-env ctx ST)]
    T))

(defimplicit set-elem
  "The set `x` is an element of the powerset `X`, cf. [[set-elem-def]]."
  [def-env ctx [x x-ty] [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-elem-def T x X)))

(definition set-ex-def
  "The powerset existential.
This is the definition of [[latte.quant/ex]] but
adpated for sets."
  [[T :type] [X (powerset T)]]
  (forall [α :type]
    (==> (forall [x (set T)]
           (==> (set-elem x X) α))
         α)))

(defimplicit set-ex
  "There exists an element set `s` of the powerset `X` such that... cf. [[set-ex-def]]."
  [def-env ctx [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-ex-def T X)))

(defthm set-ex-elim-thm
  "The elimination rule for the set existential."
  [[T :type] [X (powerset T)] [A :type]]
  (==> (set-ex X)
       (forall [x (set T)]
         (==> (set-elem x X) A))
       A))

(proof 'set-ex-elim-thm :script
  (assume [H1 (set-ex X)
           H2 (forall [x (set T)] (==> (set-elem x X) A))]
    (have <a> (==> (forall [x (set T)]
                           (==> (set-elem x X) A))
                   A) :by (H1 A))
    (have <b> A :by (<a> H2)))
  (qed <b>))

(defimplicit set-ex-elim
  "The elimination rule for the set existential, cf. [[set-ex-elim-thm]]."
  [def-env ctx [X X-ty] [A A-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-ex-elim-thm T X A)))

(defthm set-ex-intro-thm
  "Introduction rule for [[set-ex]]."
  [[T :type] [X (powerset T)] [x (set T)]]
  (==> (set-elem x X)
       (set-ex X)))

(proof 'set-ex-intro-thm
    :script
  (assume [H (set-elem x X)
           A :type
           Q (forall [y (set T)] (==> (set-elem y X) A))]
    (have <a> (==> (set-elem x X) A) :by (Q x))
    (have <b> A :by (<a> H)))
  (qed <b>))

(defimplicit set-ex-intro
  "Introduction rule for set existential, cf. [[set-ex-intro-thm]]."
  [def-env ctx [X X-ty] [x x-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-ex-intro-thm T X x)))

(definition set-single-def
  "The powerset version of [[latte.quant/single]].
There exists at most one set ..."
  [[T :type] [X (powerset T)]]
  (forall [x y (set T)]
    (==> (set-elem x X)
         (set-elem y X)
         (seteq x y))))

(defimplicit set-single
  "There is a single set element in `X` such that...
cf. [[set-single-def]]"
  [def-env ctx [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-single-def T X)))

(definition set-unique-def
  "The powerset version of [[latte.quant/unique]].
There exists a unique set ..."
  [[T :type] [X (powerset T)]]
  (and (set-ex X)
       (set-single X)))

(defimplicit set-unique
  "There exists a unique set element in `X` such that...
cf. [[set-unique-def]]"
  [def-env ctx [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'set-unique-def T X)))

(defaxiom the-set-ax
  "The powerset version of [[latte.quant/the]]."
  [[T :type] [X (powerset T)] [u (set-unique X)]]
  (set T))

(defimplicit the-set
  "The unique descriptor for powerset `X`, cf. [[the-set-ax]]."
  [def-env ctx [X X-ty] [u u-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'the-set-ax T X u)))

(defaxiom the-set-prop
  "The property of the unique set descriptor [[the-set]]."
  [[T :type] [X (powerset T)] [u (set-unique X)]]
  (set-elem (the-set X u) X))

(defthm the-set-lemma
  "The unique set ... is unique."
  [[T :type] [X (powerset T)] [u (set-unique X)]]
  (forall [y (set T)]
    (==> (set-elem y X)
         (seteq y (the-set X u)))))

(proof 'the-set-lemma
    :script
  (have <a> (set-single X) :by (p/and-elim-right u))
  (have <b> (set-elem (the-set X u) X) :by (the-set-prop T X u))
  (assume [y (set T)
           Hy (set-elem y X)]
    (have <c> (==> (set-elem y X)
                   (set-elem (the-set X u) X)
                   (seteq y (the-set X u))) :by (<a> y (the-set X u)))
    (have <d> (seteq y (the-set X u)) :by (<c> Hy <b>)))
  (qed <d>))

(definition unions-def
  "Generalized union.
This is the set {y:T | ∃x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
          (set-ex (lambda [x (set T)]
                          (and (set-elem x X)
                               (elem y x))))))

(defimplicit unions
  "Generalized union.
This is the set {y:T | ∃x∈X, y∈x}."
  [def-env ctx [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'unions-def T X)))

(defthm unions-upper-bound
   "The generalized union is an upper bound wrt. 
the subset relation."
   [[T :type] [X (powerset T)]]
   (forall [x (set T)]
     (==>  (set-elem x X)
           (subset x (unions X)))))

(proof 'unions-upper-bound
    :script
  (assume [x (set T)
           Hx (set-elem x X)]
    (assume [y T
             Hy (elem y x)]
      (pose I := (lambda [x (set T)]
                         (and (set-elem x X)
                              (elem y x))))
      (have <a> (set-elem x I) :by (p/and-intro Hx Hy))
      (have <b> (elem y (unions X)) :by ((set-ex-intro I x) <a>))))
  (qed <b>))

(definition intersections-def
  "Generalize intersections.
This is the set {y:T | ∀x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
    (forall [x (set T)]
      (==> (set-elem x X)
           (elem y x)))))

(defimplicit intersections
  "Generalize intersections.
This is the set {y:T | ∀x∈X, y∈x}."
  [def-env ctx [X X-ty]]
  (let [T (fetch-powerset-type def-env ctx X-ty)]
    (list #'intersections-def T X)))

(defthm intersections-lower-bound
  "The generalized intersection is a lower bound wrt. the subset relation."
  [[T :type] [X (powerset T)]]
  (forall [x (set T)]
    (==> (set-elem x X)
         (subset (intersections X) x))))

(proof 'intersections-lower-bound
    :script
  (assume [x (set T)
           Hx (set-elem x X)]
    (assume [y T
             Hy (elem y (intersections X))]
      (have <a> (elem y x) :by (Hy x Hx))))
  (qed <a>))

(defthm intersections-prop
  "Preservation of properties on intersections."
  [[T :type] [P (==> T :type)] [X (powerset T)]]
  (forall [x (set T)]
    (==> (set-elem x X)
         (forall [y T]
           (==> (elem y x)
                (P y)))
         (forall [z T]
           (==> (elem z (intersections X))
                (P z))))))

(proof 'intersections-prop
    :script
  (assume [x (set T)
           H1 (set-elem x X)
           H2 (forall [y T]
                (==> (elem y x)
                     (P y)))]
    (assume [z T
             Hz (elem z (intersections X))]
      (have <a> (==> (elem z x)
                     (P z)) :by (H2 z))
      (have <b> (elem z x)
            :by ((intersections-lower-bound T X) x H1 z Hz))
      (have <c> (P z) :by (<a> <b>))))
  (qed <c>))


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
    :script
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
    :script
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
    :script
  (assume [H (not (s/set-equal x (s/emptyset T)))]
    (have <a> (set-elem x (powerset1 T)) :by H))
  (qed <a>))

(defthm powerset1-prop-conv
  [[T :type] [x (set T)]]
  (==> (set-elem x (powerset1 T))
       (not (s/set-equal x (s/emptyset T)))))

(proof 'powerset1-prop-conv
    :script
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
    :script
  (have <a> _ :by (p/and-intro (powerset1-prop T x)
                               (powerset1-prop-conv T x)))
  (qed <a>))

