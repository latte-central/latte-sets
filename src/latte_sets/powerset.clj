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

              [latte-sets.core :as s :refer [set elem seteq subset]]))

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
  "The elimination rule for the set existential."
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

(defthm set-ex-intro
  "Introduction rule for [[ex-set]]."
  [[T :type] [X (powerset T)] [x (set T)]]
  (==> (set-elem T x X)
       (set-ex T X)))

(proof set-ex-intro
    :script
  (assume [H (set-elem T x X)
           A :type
           Q (forall [y (set T)] (==> (set-elem T y X) A))]
    (have a (==> (set-elem T x X) A) :by (Q x))
    (have b A :by (a H))
    (qed b)))

(definition set-single
  "The powerset version of [[latte.quant/single]].
There exists at most one set ..."
  [[T :type] [X (powerset T)]]
  (forall [x y (set T)]
    (==> (set-elem T x X)
         (set-elem T y X)
         (seteq T x y))))

(definition set-unique
  "The powerset version of [[latte.quant/unique]].
There exists a unique set ..."
  [[T :type] [X (powerset T)]]
  (and (set-ex T X)
       (set-single T X)))

(defaxiom the-set
  "The powerset version of [[latte.quant/the]]."
  [[T :type] [X (powerset T)] [u (set-unique T X)]]
  (set T))

(defaxiom the-set-prop
  "The property of the unique set descriptor [[the-set]]."
  [[T :type] [X (powerset T)] [u (set-unique T X)]]
  (set-elem T (the-set T X u) X))

(defthm the-set-lemma
  "The unique set ... is unique."
  [[T :type] [X (powerset T)] [u (set-unique T X)]]
  (forall [y (set T)]
    (==> (set-elem T y X)
         (seteq T y (the-set T X u)))))

(proof the-set-lemma
    :script
  (have a (set-single T X) :by (p/and-elim-right% u))
  (have b (set-elem T (the-set T X u) X) :by (the-set-prop T X u))
  (assume [y (set T)
           Hy (set-elem T y X)]
    (have c (==> (set-elem T y X)
                 (set-elem T (the-set T X u) X)
                 (seteq T y (the-set T X u))) :by (a y (the-set T X u)))
    (have d (seteq T y (the-set T X u)) :by (c Hy b)))
  (qed d))


(definition unions
  "Generalized union.
This is the set {y:T | ∃x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
    (set-ex T (lambda [x (set T)]
                (and (set-elem T x X)
                     (elem T y x))))))

(defthm unions-upper-bound
   "The generalized union is an upper bound wrt. 
the subset relation."
   [[T :type] [X (powerset T)]]
   (forall [x (set T)]
     (==>  (set-elem T x X)
           (subset T x (unions T X)))))

(proof unions-upper-bound
    :script
  (assume [x (set T)
           Hx (set-elem T x X)]
    (assume [y T
             Hy (elem T y x)]
      (have I _ :by (lambda [x (set T)]
                      (and (set-elem T x X)
                           (elem T y x))))
      (have a (set-elem T x I) :by (p/and-intro% Hx Hy))
      (have b (elem T y (unions T X)) :by ((set-ex-intro T I x) a)))
    (qed b)))

(definition intersections
  "Generalize intersections.
This is the set {y:T | ∀x∈X, y∈x}."
  [[T :type] [X (powerset T)]]
  (lambda [y T]
    (forall [x (set T)]
      (==> (set-elem T x X)
           (elem T y x)))))

(defthm intersections-lower-bound
  "The generalized intersection is a lower bound wrt. the subset relation."
  [[T :type] [X (powerset T)]]
  (forall [x (set T)]
    (==> (set-elem T x X)
         (subset T (intersections T X) x))))

(proof intersections-lower-bound
    :script
  (assume [x (set T)
           Hx (set-elem T x X)]
    (assume [y T
             Hy (elem T y (intersections T X))]
      (have a (elem T y x) :by (Hy x Hx)))
    (qed a)))

(defthm intersections-prop
  "Preservation of properties on intersections."
  [[T :type] [P (==> T :type)] [X (powerset T)]]
  (forall [x (set T)]
    (==> (set-elem T x X)
         (forall [y T]
           (==> (elem T y x)
                (P y)))
         (forall [z T]
           (==> (elem T z (intersections T X))
                (P z))))))

(proof intersections-prop
    :script
  (assume [x (set T)
           H1 (set-elem T x X)
           H2 (forall [y T]
                (==> (elem T y x)
                     (P y)))]
    (assume [z T
             Hz (elem T z (intersections T X))]
      (have <a> (==> (elem T z x)
                     (P z)) :by (H2 z))
      (have <b> (elem T z x)
            :by ((intersections-lower-bound T X) x H1 z Hz))
      (have <c> (P z) :by (<a> <b>)))
    (qed <c>)))


