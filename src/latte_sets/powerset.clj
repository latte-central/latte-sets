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
                                            forall lambda ==>
                                            assume have proof lambda]]
              [latte.quant :as q :refer [exists]]
              [latte.prop :as p :refer [<=> and or not]]
              [latte.equal :as eq :refer [equal]]

              [latte-sets.core :as s :refer [set elem]]))

(definition powerset
  "The powerset constructor. 

The term `(powerset T)' is the type 
of sets whose elements are sets of type `T`."
  [[T :type]]
  (==> (set T) :type))

(definition set-elem
  "Membership for powersets.
Th set `x` is an element of the powerset `X`."
  [[T :type] [x (set T)] [X (powerset T)]]
  (X x))

(definition set-ex
  "The powerset existential.
This is the definition of [[latte.quant/ex]] but
adpated for sets."
  [[T :type] [X (powerset T)]]
  (forall [α :type]
    (==> (forall [x (set T)]
           (==> (set-elem T x X) α))
         α)))

(defthm set-ex-elim
  "The ()elimination rule for the set existential."
  [[T :type] [X (powerset T)] [A :type]]
  (==> (set-ex T X)
       (forall [x (set T)]
         (==> (set-elem T x X) A))
       A))

(proof set-ex-elim :script
  (assume [H1 (set-ex T X)
           H2 (forall [x (set T)] (==> (set-elem T x X) A))]
    (have a (==> (forall [x (set T)]
                   (==> (set-elem T x X) A))
                 A) :by (H1 A))

    (have b A :by (a H2))
    (qed b)))

(defthm ex-set-intro
  "Introduction rule for [[ex-set]]."
  [[T :type] [X (powerset T)] [x (set T)]]
  (==> (set-elem T x X)
       (set-ex T X)))

(proof ex-set-intro
    :script
  (assume [H (set-elem T x X)
           A :type
           Q (forall [y (set T)] (==> (set-elem T y X) A))]
    (have a (==> (set-elem T x X) A) :by (Q x))
    (have b A :by (a H))
    (have c _ :discharge [A Q b])
    (qed c)))

(definition unions
  "Generalized union.
This is the set {y:T | ∃x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
    (set-ex T (lambda [x (set T)]
                (and (set-elem T x X)
                     (elem T y x))))))

(definition intersections
  "Generalize intersections.
This is the set {y:T | ∀x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
    (forall [x (set T)]
      (==> (set-elem T x X)
           (elem T y x)))))







