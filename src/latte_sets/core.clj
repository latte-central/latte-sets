(ns latte-sets.core
  "Set-theoretic notions based on the subset
  approach of type theory.

  The main idea is to consider a typed variant of
  a mathematical set as a predicate over a given type.

  What is called a **set** will be technically-speaking
  a subset of a type, hence a predicate over a given type.
  This means that the set theory developed here is *typed*
  and thus quite different than the standard axiomatic
set theories (e.g. ZF and ZFC), which are essentially untyped.

  But many set-theoretic constructions and results have a
natural translation to the typed setting.
"

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          forall lambda
                                          assume have pose proof]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]))

(definition set
  "The type of sets whose elements are of type `T`."
  [[T :type]]
  (==> T :type))

(definition elem-def
  "Set membership. 

Given a type `T`, a value `x` of type `T` and
 a set `s`, then `(elem T x s)` means that `x` is an element of set `s`.
 The standard mathematical notation is: `x`∊`s` (leaving the type `T` implicit)."
  [[T :type] [x T] [s (set T)]]
  (s x))

(defnotation forall-in
  "Universal quantification over sets.

  `(forall-in [x T s] (P x))` is a 
shortcut for `(forall [x T]
                 (==> (elem T x s)
                      (P x)))`."
  [binding body]
  (if (not= (count binding) 3)
    [:ko {:msg "Binding of `forall-in` should be of the form `[x T s]`."
          :binding binding}]
    [:ok `(forall [~(first binding) ~(second binding)]
                  (==> (elem ~(second binding) ~(first binding) ~(nth binding 2))
                       ~body))]))

(alter-meta! #'forall-in update-in [:style/indent] (fn [_] [1 :form :form]))

(defnotation exists-in
  "Existential quantification over sets.

  `(exists-in [x T s] (P x))` is a 
shortcut for `(exists [x T]
                 (and (elem T x s)
                      (P x)))`."
  [binding body]
  (if (not= (count binding) 3)
    [:ko {:msg "Binding of `exists-in` should be of the form `[x T s]`."
          :binding binding}]
    [:ok `(exists [~(first binding) ~(second binding)]
                  (and (elem ~(second binding) ~(first binding) ~(nth binding 2))
                       ~body))]))

(alter-meta! #'exists-in update-in [:style/indent] (fn [_] [1 :form :form]))

(definition fullset
  "The full set of a type
(all the inhabitants of the type are element
of the full set)."
  [[T :type]]
  (lambda [x T] p/truth))

(defthm fullset-intro
  "Introduction rule for the full set."
  [[T :type]]
  (forall [x T]
    (elem T x (fullset T))))

(proof fullset-intro :script
  (assume [x T]
    (have a (elem T x (fullset T)) :by p/truth-is-true)
    (qed a)))

(definition emptyset
  "The empty set of a type."
  [[T :type]]
  (lambda [x T] p/absurd))

(defthm emptyset-prop
  "The main property of the empty set."
  [[T :type]]
  (forall [x T]
    (not (elem T x (emptyset T)))))

(proof emptyset-prop :script
  (assume [x T
           H (elem T x (emptyset T))]
    (have a p/absurd :by H)
    (qed a)))


(definition subset
  "The subset relation for type `T`.

The expression `(subset T s1 s2)` means that
 the set `s1` is a subset of `s2`, i.e. `s1`⊆`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (forall [x T]
    (==> (elem T x s1)
         (elem T x s2))))

(defthm subset-refl
  "The subset relation is reflexive."
  [[T :type] [s (set T)]]
  (subset T s s))

(proof subset-refl :script
  (assume [x T
           H (elem T x s)]
    (have a (elem T x s) :by H)
    (qed a)))

(defthm subset-trans
  "The subset relation is transitive."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (subset T s1 s2)
       (subset T s2 s3)
       (subset T s1 s3)))

(proof subset-trans :script
  (assume [H1 (subset T s1 s2)
           H2 (subset T s2 s3)]
    (assume [x T]
      (have a (==> (elem T x s1)
                   (elem T x s2)) :by (H1 x))
      (have b (==> (elem T x s2)
                   (elem T x s3)) :by (H2 x))
      (have c (==> (elem T x s1)
                   (elem T x s3)) :by (p/impl-trans% a b)))
    (qed c)))

(defthm subset-prop
  "Preservation of properties on subsets."
  [[T :type] [P (==> T :type)][s1 (set T)] [s2 (set T)]]
  (==> (forall [x T]
         (==> (elem T x s2)
              (P x)))
       (subset T s1 s2)
       (forall [x T]
         (==> (elem T x s1)
              (P x)))))

(proof subset-prop
    :script
  (assume [H1 (forall [x T]
                (==> (elem T x s2)
                     (P x)))
           H2 (subset T s1 s2)]
    (assume [x T
             Hx (elem T x s1)]
      (have <a> (elem T x s2) :by (H2 x Hx))
      (have <b> (P x) :by (H1 x <a>)))
    (qed <b>)))

(defthm subset-emptyset-lower-bound
  "The emptyset is a subset of every other sets."
  [[T :type] [s (set T)]]
  (subset T (emptyset T) s))

(proof subset-emptyset-lower-bound
    :script
  (assume [x T
           Hx (elem T x (emptyset T))]
    (have <a> p/absurd :by Hx)
    (have <b> (elem T x s) :by ((p/ex-falso (elem T x s)) <a>))
    (qed <b>)))

(defthm subset-fullset-upper-bound
  "The fullset is a superset of every other sets."
  [[T :type] [s (set T)]]
  (subset T s (fullset T)))

(proof subset-fullset-upper-bound
    :script
  (assume [x T
           Hx (elem T x s)]
    (have <a> (elem T x (fullset T))
          :by p/truth-is-true)
    (qed <a>)))

(definition seteq
  "Equality on sets.

This is a natural equality on sets based on the subset relation."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (and (subset T s1 s2)
       (subset T s2 s1)))

(defthm seteq-refl
  "Set equality is reflexive."
  [[T :type] [s (set T)]]
  (seteq T s s))

(proof seteq-refl :script
  (have a (subset T s s) :by (subset-refl T s))
  (have b (and (subset T s s)
               (subset T s s))
        :by ((p/and-intro (subset T s s)
                          (subset T s s)) a a))
  (qed b))

(defthm seteq-sym
  "Set equality is symmetric."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (seteq T s1 s2)
       (seteq T s2 s1)))

(proof seteq-sym :script
  (assume [H (seteq T s1 s2)]
    (have a (subset T s1 s2) :by (p/and-elim-left% H))
    (have b (subset T s2 s1) :by (p/and-elim-right% H))
    (have c (seteq T s2 s1) :by (p/and-intro% b a))
    (qed c)))

(defthm seteq-trans
  "Set equality is transitive."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (seteq T s1 s2)
       (seteq T s2 s3)
       (seteq T s1 s3)))

(proof seteq-trans :script
  (assume [H1 (seteq T s1 s2)
           H2 (seteq T s2 s3)]
    (have a1 (subset T s1 s2) :by (p/and-elim-left% H1))
    (have b1 (subset T s2 s3) :by (p/and-elim-left% H2))
    (have c1 (subset T s1 s3) :by ((subset-trans T s1 s2 s3) a1 b1))
    (have a2 (subset T s2 s1) :by (p/and-elim-right% H1))
    (have b2 (subset T s3 s2) :by (p/and-elim-right% H2))
    (have c2 (subset T s3 s1) :by ((subset-trans T s3 s2 s1) b2 a2))
    (have d (seteq T s1 s3) :by (p/and-intro% c1 c2))
    (qed d)))

(definition set-equal
  "A *Leibniz*-stype equality for sets.

It says that two sets `s1` and `s2` are equal iff for 
any predicate `P` then `(P s1)` if and only if `(P s2)`.

Note that the identification with [[seteq]] is non-trivial,
 and requires an axiom."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (forall [P (==> (set T) :type)]
    (<=> (P s1) (P s2))))

(defthm set-equal-prop
  [[T :type] [s1 (set T)] [s2 (set T)] [P (==> (set T) :type)]]
  (==> (set-equal T s1 s2)
       (P s1)
       (P s2)))

(proof set-equal-prop
    :script
  (assume [Heq (set-equal T s1 s2)
           Hs1 (P s1)]
    (have <a> (<=> (P s1) (P s2))
          :by (Heq P))
    (have <b> (==> (P s1) (P s2))
          :by (p/and-elim-left% <a>))
    (have <c> (P s2) :by (<b> Hs1))
    (qed <c>)))

(defthm set-equal-refl
  "Reflexivity of set equality."
  [[T :type] [s (set T)]]
  (set-equal T s s))

(proof set-equal-refl :script
  (assume [P (==> (set T) :type)]
    (have a (<=> (P s) (P s))
          :by (p/iff-refl (P s)))
    (qed a)))

(defthm set-equal-sym
  "Symmetry of set equality."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (set-equal T s1 s2)
       (set-equal T s2 s1)))

(proof set-equal-sym :script
  (assume [H (set-equal T s1 s2)
           Q (==> (set T) :type)]
    (have a (<=> (Q s1) (Q s2)) :by (H Q))
    (have b (<=> (Q s2) (Q s1)) :by ((p/iff-sym (Q s1) (Q s2)) a))
    (qed b)))

(defthm set-equal-trans
  "Transitivity of set equality."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (set-equal T s1 s2)
       (set-equal T s2 s3)
       (set-equal T s1 s3)))

(proof set-equal-trans :script
  (assume [H1 (set-equal T s1 s2)
           H2 (set-equal T s2 s3)
           Q (==> (set T) :type)]
    (have a (<=> (Q s1) (Q s2)) :by (H1 Q))
    (have b (<=> (Q s2) (Q s3)) :by (H2 Q))
    (have c (<=> (Q s1) (Q s3))
          :by ((p/iff-trans (Q s1) (Q s2) (Q s3)) a b))
    (qed c)))

(defthm set-equal-implies-subset
  "Going from *Leibniz* equality on sets to the subset relation is easy."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (set-equal T s1 s2)
       (subset T s1 s2)))

(proof set-equal-implies-subset :script
  (assume [H (set-equal T s1 s2)
           x T]
    (pose Qx := (lambda [s (set T)]
                       (elem T x s)))
    (have a (<=> (elem T x s1) (elem T x s2))
          :by (H Qx))
    (have b (==> (elem T x s1) (elem T x s2))
          :by ((p/iff-elim-if (elem T x s1) (elem T x s2)) a))
    (qed b)))

(defthm set-equal-implies-seteq
  "Subset-based equality implies *Leibniz*-style equality on sets."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (set-equal T s1 s2)
       (seteq T s1 s2)))

(proof set-equal-implies-seteq :script
  (assume [H (set-equal T s1 s2)]
    ;; "First we get s1⊆s2."
    (have a (subset T s1 s2) :by ((set-equal-implies-subset T s1 s2) H))
    ;; "Then we get s2⊆s1."
    (have b1 (set-equal T s2 s1) :by ((set-equal-sym T s1 s2) H))
    (have b (subset T s2 s1) :by ((set-equal-implies-subset T s2 s1) b1))
    ;; "... and we can now conclude"
    (have c (seteq T s1 s2) :by (p/and-intro% a b))
    (qed c)))

(defaxiom seteq-implies-set-equal-ax
  "Going from subset-based equality to *Leibniz*-style equality
requires this axiom. This is because we cannot lift membership
 to an arbitrary predicate."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (seteq T s1 s2)
       (set-equal T s1 s2)))

(defthm set-equal-seteq
  "Set equality and subset-based equality (should) coincide (axiomatically)."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (<=> (seteq T s1 s2)
       (set-equal T s1 s2)))

(proof set-equal-seteq :script
  (have a (==> (seteq T s1 s2)
               (set-equal T s1 s2)) :by (seteq-implies-set-equal-ax T s1 s2))
  (have b (==> (set-equal T s1 s2)
               (seteq T s1 s2)) :by (set-equal-implies-seteq T s1 s2))
  (qed ((p/iff-intro (seteq T s1 s2)
                     (set-equal T s1 s2)) a b)))

(definition psubset
  "The anti-reflexive variant of the subset relation.

The expression `(psubset T s1 s2)` means that
 the set `s1` is a subset of `s2`, but that the two
sets are distinct, i.e. `s1`⊂`s2` (or more explicitely `s1`⊊`s2`)."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (and (subset T s1 s2)
       (not (seteq T s1 s2))))

(defthm psubset-antirefl
  [[T :type] [s (set T)]]
  (not (psubset T s s)))

(proof psubset-antirefl
    :script
  (assume [H (psubset T s s)]
    (have <a> (not (seteq T s s))
          :by (p/and-elim-right% H))
    (have <b> (seteq T s s) :by (seteq-refl T s))
    (have <c> p/absurd :by (<a> <b>))
    (qed <c>)))

(defthm psubset-antisym
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (not (and (psubset T s1 s2)
            (psubset T s2 s1))))

(proof psubset-antisym
    :script
  (assume [H (and (psubset T s1 s2)
                  (psubset T s2 s1))]
    (have <a> (not (seteq T s1 s2))
          :by (p/and-elim-right% (p/and-elim-left% H)))
    (have <b> (subset T s1 s2)
          :by (p/and-elim-left% (p/and-elim-left% H)))
    (have <c> (subset T s2 s1)
          :by (p/and-elim-left% (p/and-elim-right% H)))
    (have <d> (seteq T s1 s2)
          :by (p/and-intro% <b> <c>))
    (have <e> p/absurd :by (<a> <d>))
    (qed <e>)))

(defthm psubset-trans
  "The proper subset relation is transitive."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (==> (psubset T s1 s2)
       (psubset T s2 s3)
       (psubset T s1 s3)))

(proof psubset-trans :script
  (assume [H1 (psubset T s1 s2)
           H2 (psubset T s2 s3)]
    (have <a> (subset T s1 s3)
          :by ((subset-trans T s1 s2 s3)
               (p/and-elim-left% H1)
               (p/and-elim-left% H2)))
    (assume [H (seteq T s1 s3)]
      (have <b> (set-equal T s1 s3)
            :by ((seteq-implies-set-equal-ax T s1 s3)
                 H))
      (have <c> (psubset T s3 s2)
            :by ((set-equal-prop T s1 s3 (lambda [x (set T)]
                                           (psubset T x s2)))
                 <b> H1))
      (have <d> p/absurd
            :by ((psubset-antisym T s2 s3)
                 (p/and-intro% H2 <c>))))
    (have <e> _ :by (p/and-intro% <a> <d>))
    (qed <e>)))

(defthm psubset-emptyset
  [[T :type] [s (set T)]]
  (==> (psubset T (emptyset T) s)
       (not (seteq T s (emptyset T)))))

(proof psubset-emptyset
    :script
  (assume [H (psubset T (emptyset T) s)]
    (assume [H' (seteq T s (emptyset T))]
      (have <a> (not (seteq T (emptyset T) s))
            :by (p/and-elim-right% H))
      (have <b> (seteq T (emptyset T) s)
            :by ((seteq-sym T s (emptyset T)) H'))
      (have <c> p/absurd :by (<a> <b>))
      (qed <c>))))

(defthm psubset-emptyset-conv
  [[T :type] [s (set T)]]
  (==> (not (seteq T s (emptyset T)))
       (psubset T (emptyset T) s)))

(proof psubset-emptyset-conv
    :script
  (assume [H (not (seteq T s (emptyset T)))]
    (have <a> (subset T (emptyset T) s)
          :by (subset-emptyset-lower-bound T s))
    (assume [H' (seteq T (emptyset T) s)]
      (have <b> (seteq T s (emptyset T))
            :by ((seteq-sym T (emptyset T) s) H'))
      (have <c> p/absurd :by (H <b>)))
    (have <d> (psubset T (emptyset T) s)
          :by (p/and-intro% <a> <c>))
    (qed <d>)))

(defthm psubset-emptyset-equiv
  [[T :type] [s (set T)]]
  (<=> (psubset T (emptyset T) s)
       (not (seteq T s (emptyset T)))))

(proof psubset-emptyset-equiv
    :script
  (have <a> _ :by (p/and-intro% (psubset-emptyset T s)
                                (psubset-emptyset-conv T s)))
  (qed <a>))

