(ns latte-sets.set
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

  (:refer-clojure :exclude [and or not set remove])

  (:require [latte.core :as latte :refer [definition try-definition
                                          defthm defaxiom defnotation
                                          defimplicit deflemma
                                          forall lambda
                                          assume have pose proof try-proof qed]]
            [latte.utils :as u]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.classic :as classic]))

(definition set
  "The type of sets whose elements are of type `T`."
  [T :type]
  (==> T :type))

(defn fetch-set-type [def-env ctx s-type]
  "Fetch the `T` in a set-type `s-type` of the form `(set T)` (fails otherwise).
This function is used for implicit in sets."
  (let [[T _] (p/decompose-impl-type def-env ctx s-type)]
    T))

;; Implicit type parameter: to infer `T` from `(set ?T)`
(u/register-implicit-type-parameters-handler! 'set fetch-set-type 1)

(defnotation set-of
  "Definition of a set by comprehension.

  `(set-of [x T] (P x))` is the set of all `x`'s of type `T` such
 that `(P x)`. This is similar to the notation `{x : T | P(x) }` in classical mathematics.

Note that it is exactly the same as `(lambda [x T] (P x))`"
  [binding body]
  (if (not= (count binding) 2)
    [:ko {:msg "Binding of `set-of` should be of the form `[x T]`."
          :binding binding}]
    [:ok (list 'lambda [(first binding) (second binding)] body)]))

(definition elem-def
  "Set membership. 

 `(elem x s)` means that `x` (of implicit type `T`) is an element of set `s`.
 The standard mathematical notation is: `x`∊`s`."
  [[T :type] [x T] [s (set T)]]
  (s x))

(defimplicit elem
  "`(elem x s)` means `x` is an element of set `s`, cf. [[elem-def]]."
  [def-env ctx [x x-ty] [s s-ty]]
  (with-meta (list #'elem-def x-ty x s) {::elem-set s}))

(defimplicit element-type-of
  "Replaces `sterm` by its element type (if it is a set type)."
  [def-env ctx [sterm stype]]
  (fetch-set-type def-env ctx stype))

(definition fullset
  "The full set of a type
(all the inhabitants of the type are element
of the full set)."
  [T :type]
  (set-of [x T] p/truth))

(defthm fullset-intro
  "Introduction rule for the full set."
  [T :type]
  (forall [x T]
    (elem x (fullset T))))

(proof 'fullset-intro
  (assume [x T]
    (have <a> (elem x (fullset T)) :by p/truth-is-true))
  (qed <a>))

(definition emptyset
  "The empty set of a type."
  [T :type]
  (set-of [x T] p/absurd))

(defthm emptyset-prop
  "The main property of the empty set."
  [T :type]
  (forall [x T]
    (not (elem x (emptyset T)))))

(proof 'emptyset-prop
  (assume [x T
           H (elem x (emptyset T))]
    (have <a> p/absurd :by H))
  (qed <a>))


(definition singleton
  "The singleton set {x}."
  [?T :type, x T]
  (set-of [y T] (equal y x)))

(defthm singleton-elem
  [?T :type, x T]
  (elem x (singleton x)))

(proof 'singleton-elem-thm
  (qed (eq/eq-refl x)))

(definition subset
  "The subset relation for type `T`.
The expression `(subset-def T s1 s2)` means that
 the set `s1` is a subset of `s2`, i.e. `s1`⊆`s2`."
  [?T :type, [s1 s2 (set T)]]
  (forall [x T]
    (==> (elem x s1)
         (elem x s2))))

(defthm subset-refl
  "The subset relation is reflexive."
  [?T :type, s (set T)]
  (subset s s))

(proof 'subset-refl-thm
  (assume [x T
           H (elem x s)]
    (have <a> (elem x s) :by H))
  (qed <a>))

(defthm subset-trans
  "The subset relation is transitive."
  [?T :type, [s1 s2 s3 (set T)]]
  (==> (subset s1 s2)
       (subset s2 s3)
       (subset s1 s3)))

(proof 'subset-trans-thm
  (assume [H1 (subset s1 s2)
           H2 (subset s2 s3)]
    (assume [x T]
      (have <a> (==> (elem x s1)
                     (elem x s2)) :by (H1 x))
      (have <b> (==> (elem x s2)
                     (elem x s3)) :by (H2 x))
      (have <c> (==> (elem x s1)
                     (elem x s3)) :by (p/impl-trans <a> <b>))))
  (qed <c>))

(defthm subset-prop
  "Preservation of properties on subsets."
  [?T :type, P (==> T :type), [s1 s2 (set T)]]
  (==> (forall [x T]
         (==> (elem x s2)
              (P x)))
       (subset s1 s2)
       (forall [x T]
         (==> (elem x s1)
              (P x)))))

(proof 'subset-prop-thm
  (assume [H1 (forall [x T]
                      (==> (elem x s2)
                           (P x)))
           H2 (subset s1 s2)]
    (assume [x T
             Hx (elem x s1)]
      (have <a> (elem x s2) :by (H2 x Hx))
      (have <b> (P x) :by (H1 x <a>))))
  (qed <b>))

(defthm subset-emptyset-lower-bound
  "The emptyset is a subset of every other sets."
  [?T :type, s (set T)]
  (subset (emptyset T) s))

(proof 'subset-emptyset-lower-bound-thm
  (assume [x T
           Hx (elem x (emptyset T))]
    (have <a> p/absurd :by Hx)
    (have <b> (elem x s) :by ((p/ex-falso (elem x s)) <a>)))
  (qed <b>))

(defthm emptyset-subset-intro
  [?T :type, s (set T)]
  (==> (forall [x T] (not (elem x s)))
       (subset s (emptyset T))))

(proof 'emptyset-subset-intro-thm
  (assume [H _
           x T Hx (elem x s)]
    (have <a> p/absurd :by (H x Hx))
    (have <b> (elem x (emptyset T))
          :by (<a> (elem x (emptyset T)))))
  (qed <b>))

(defthm subset-fullset-upper-bound
  "The fullset is a superset of every other sets."
  [?T :type, s (set T)]
  (subset s (fullset T)))

(proof 'subset-fullset-upper-bound-thm
  (assume [x T
           Hx (elem x s)]
    (have <a> (elem x (fullset T))
          :by p/truth-is-true))
  (qed <a>))

(defthm subset-intro
  "Introduction rule for subset relation."
  [?T :type, [s1 s2 (set T)]]
  (==> (forall [x T]
               (==> (elem x s1)
                    (elem x s2)))
       (subset s1 s2)))

(proof 'subset-intro-thm
  (assume [H (forall [x T]
               (==> (elem x s1)
                    (elem x s2)))]
    (have <a> (subset s1 s2) :by H))
  (qed <a>))

(defthm subset-elim
  "Elimination rule for subset relation."
  [?T :type, [s1 s2 (set T)], x T]
  (==> (elem x s1)
       (subset s1 s2)
       (elem x s2)))

(proof 'subset-elim-thm
  (assume [H1 (elem x s1)
           H2 (subset s1 s2)]
    (have <a> (elem x s2) :by (H2 x H1)))
  (qed <a>))

;; now that we have intro and elim, subset can become opaque
;; (u/set-opacity! #'subset-def true)
;; not yet read (cf. algebra)

(definition seteq
  "Set equivalence. Set `s1` is equal to `s2`
This is a natural notion of \"equal sets\"
 based on the subset relation."
  [?T :type, [s1 s2 (set T)]]
  (and (subset s1 s2)
       (subset s2 s1)))

(defthm seteq-refl
  "Set equality is reflexive."
  [?T :type, s (set T)]
  (seteq s s))

(proof 'seteq-refl-thm
  (have <a> (subset s s) :by (subset-refl s))
  (have <b> (and (subset s s)
                 (subset s s))
        :by (p/and-intro <a> <a>))
  (qed <b>))

(defthm seteq-sym
  "Set equality is symmetric."
  [?T :type, [s1 s2 (set T)]]
  (==> (seteq s1 s2)
       (seteq s2 s1)))

(proof 'seteq-sym-thm
  (assume [H (seteq s1 s2)]
    (have <a> (subset s1 s2) :by (p/and-elim-left H))
    (have <b> (subset s2 s1) :by (p/and-elim-right H))
    (have <c> (seteq s2 s1) :by (p/and-intro <b> <a>)))
  (qed <c>))

(defthm seteq-trans
  "Set equality is transitive."
  [?T :type, [s1 s2 s3 (set T)]]
  (==> (seteq s1 s2)
       (seteq s2 s3)
       (seteq s1 s3)))

(proof 'seteq-trans-thm
  (assume [H1 (seteq s1 s2)
           H2 (seteq s2 s3)]
    (have <a1> (subset s1 s2) :by (p/and-elim-left H1))
    (have <b1> (subset s2 s3) :by (p/and-elim-left H2))
    (have <c1> (subset s1 s3) :by ((subset-trans s1 s2 s3) <a1> <b1>))
    (have <a2> (subset s2 s1) :by (p/and-elim-right H1))
    (have <b2> (subset s3 s2) :by (p/and-elim-right H2))
    (have <c2> (subset s3 s1) :by ((subset-trans s3 s2 s1) <b2> <a2>))
    (have <d> (seteq s1 s3) :by (p/and-intro <c1> <c2>)))
  (qed <d>))

(defthm emptyset-seteq-intro
  [?T :type, s (set T)]
  (==> (forall [x T] (not (elem x s)))
       (seteq s (emptyset T))))

(proof 'emptyset-seteq-intro-thm
  (assume [H _]
    (have <a> _ :by (p/and-intro ((emptyset-subset-intro s) H)
                                 (subset-emptyset-lower-bound s))))
  (qed <a>))

(definition set-equal
  "A *Leibniz*-style equality for sets.

It says that two sets `s1` and `s2` are equal iff for 
any predicate `P` then `(P s1)` if and only if `(P s2)`.

Note that the identification with [[seteq]] is non-trivial,
 and requires an axiom."
  [?T :type, [s1 s2 (set T)]]
  (forall [P (==> (set T) :type)]
          (<=> (P s1) (P s2))))

(defthm set-equal-prop
  [?T :type, [s1 s2 (set T)], P (==> (set T) :type)]
  (==> (set-equal s1 s2)
       (P s1)
       (P s2)))

(proof 'set-equal-prop-thm
  (assume [Heq (set-equal s1 s2)
           Hs1 (P s1)]
    (have <a> (<=> (P s1) (P s2))
          :by (Heq P))
    (have <b> (==> (P s1) (P s2))
          :by (p/and-elim-left <a>))
    (have <c> (P s2) :by (<b> Hs1)))
  (qed <c>))

(defthm set-equal-refl
  "Reflexivity of set equality."
  [?T :type, s (set T)]
  (set-equal s s))

(proof 'set-equal-refl-thm
  (assume [P (==> (set T) :type)]
    (have a (<=> (P s) (P s))
          :by (p/iff-refl (P s))))
  (qed a))

(defthm set-equal-sym
  "Symmetry of set equality."
  [?T :type, [s1 s2 (set T)]]
  (==> (set-equal s1 s2)
       (set-equal s2 s1)))

(proof 'set-equal-sym-thm
  (assume [H (set-equal s1 s2)
           Q (==> (set T) :type)]
    (have <a> (<=> (Q s1) (Q s2)) :by (H Q))
    (have <b> (<=> (Q s2) (Q s1)) :by (p/iff-sym <a>)))
  (qed <b>))

(defthm set-equal-trans
  "Transitivity of set equality."
  [?T :type, [s1 s2 s3 (set T)]]
  (==> (set-equal s1 s2)
       (set-equal s2 s3)
       (set-equal s1 s3)))

(proof 'set-equal-trans-thm
  (assume [H1 (set-equal s1 s2)
           H2 (set-equal s2 s3)
           Q (==> (set T) :type)]
    (have <a> (<=> (Q s1) (Q s2)) :by (H1 Q))
    (have <b> (<=> (Q s2) (Q s3)) :by (H2 Q))
    (have <c> (<=> (Q s1) (Q s3))
          :by (p/iff-trans <a> <b>)))
  (qed <c>))

(defthm set-equal-subst-prop
  "Substitutivity property of set-equality. 
This is an important elimination rule."
  [?T :type, P (==> (set T) :type), s1 (set T), s2 (set T)]
  (==> (set-equal s1 s2)
       (P s1)
       (P s2)))

(proof 'set-equal-subst-prop-thm 
  (assume [H1 (set-equal s1 s2)
           H2 (P s1)]
    (have <a> (<=> (P s1) (P s2)) :by (H1 P))
    (have <b> (P s2) :by ((p/iff-elim-if <a>) H2)))
  (qed <b>))

(defaxiom seteq-implies-set-equal
  "Going from subset-based equality to *Leibniz*-style equality
requires this axiom. This is because we cannot lift membership
 to an arbitrary predicate."
  [?T :type, [s1 s2 (set T)]]
  (==> (seteq s1 s2)
       (set-equal s1 s2)))

(defthm seteq-subst-prop
  "cf. [[set-equal-subst-prop]]"
  [?T :type, P (==> (set T) :type), s1 (set T), s2 (set T)]
  (==> (seteq s1 s2)
       (P s1)
       (P s2)))

(proof 'seteq-subst-prop-thm
  (assume [Heq _
           Hs1 _]
    (have <a> (set-equal s1 s2)
          :by ((seteq-implies-set-equal s1 s2) Heq))
    (have <b> (P s2) :by ((set-equal-subst-prop P s1 s2) <a> Hs1)))
  (qed <b>))

(defthm set-equal-implies-subset
  "Going from *Leibniz* equality on sets to the subset relation is easy."
  [?T :type, [s1 s2 (set T)]]
  (==> (set-equal s1 s2)
       (subset s1 s2)))

(proof 'set-equal-implies-subset-thm
  (assume [H (set-equal s1 s2)]
    (assume [x T]
      (pose Qx := (lambda [s (set T)]
                    (elem x s)))
      (have <a> (<=> (elem x s1) (elem x s2))
            :by (H Qx))
      (have <b> (==> (elem x s1) (elem x s2))
            :by (p/iff-elim-if <a>)))
    (have <c> (subset s1 s2) :by ((subset-intro s1 s2) <b>)))
  (qed <c>))

(defthm set-equal-implies-seteq
  "Subset-based equality implies *Leibniz*-style equality on sets."
  [?T :type, [s1 s2 (set T)]]
  (==> (set-equal s1 s2)
       (seteq s1 s2)))

(proof 'set-equal-implies-seteq-thm
  (assume [H (set-equal s1 s2)]
    ;; "First we get s1⊆s2."
    (have <a> (subset s1 s2) :by ((set-equal-implies-subset s1 s2) H))
    ;; "Then we get s2⊆s1."
    (have <b1> (set-equal s2 s1) :by ((set-equal-sym s1 s2) H))
    (have <b> (subset s2 s1) :by ((set-equal-implies-subset s2 s1) <b1>))
    ;; "... and we can now conclude"
    (have <c> (seteq s1 s2) :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm set-equal-seteq
  "Set equality and subset-based equality (should) coincide (axiomatically)."
  [?T :type, [s1 s2 (set T)]]
  (<=> (seteq s1 s2)
       (set-equal s1 s2)))

(proof 'set-equal-seteq-thm
  (have <a> (==> (seteq s1 s2)
                 (set-equal s1 s2)) :by (seteq-implies-set-equal s1 s2))
  (have <b> (==> (set-equal s1 s2)
                 (seteq s1 s2)) :by (set-equal-implies-seteq s1 s2))
  (qed (p/iff-intro <a> <b>)))

(definition non-empty
  "A non-empty set `s` of elements of type `T`"
  [?T :type, s (set T)]
  (not (subset s (emptyset T))))

(defthm non-empty-not-eq
  [?T :type, s (set T)]
  (==> (non-empty s)
       (not (seteq s (emptyset T)))))

(proof 'non-empty-not-eq-thm
  (assume [Hne (non-empty s)]
    (assume [Hcontra (seteq s (emptyset T))]
      (have <a> (subset s (emptyset T)) :by (p/and-elim-left Hcontra))
      (have <b> p/absurd :by (Hne <a>))))
  (qed <b>))

(defthm non-empty-not-equal
  [?T :type, s (set T)]
  (==> (non-empty s)
       (not (set-equal s (emptyset T)))))

(proof 'non-empty-not-equal-thm
  (assume [Hne (non-empty s)]
    (have <a> (not (seteq s (emptyset T)))
          :by ((non-empty-not-eq s) Hne))
    (assume [Hcontra (set-equal s (emptyset T))]
      (have <b> (seteq s (emptyset T))
            :by ((set-equal-implies-seteq s (emptyset T)) Hcontra))
      (have <c> p/absurd :by (<a> <b>))))
  (qed <c>))

(defthm non-empty-elem
  [?T :type, x T, s (set T)]
  (==> (elem x s)
       (non-empty s)))

(proof 'non-empty-elem-thm
  (assume [Hx (elem x s)]
    (assume [Hcontra (subset s (emptyset T))]
      (have <a> p/absurd :by (Hcontra x Hx))))
  (qed <a>))

(defthm non-empty-inhabited
  "A non-emptyset is inhabited (in classical logic)"
  [?T :type, s (set T)]
  (==> (non-empty s)
       (exists [x T] (elem x s))))

(proof 'non-empty-inhabited-thm
  (assume [Hne (non-empty s)]
    (assume [Hcontra (not (exists [x T] (elem x s)))]
      (assume [x T
               Hx (elem x s)]
        (have <a> (not (elem x s))
              :by (((q/not-ex-elim (lambda [x T] (elem x s))) Hcontra) x))
        (have <b> p/absurd :by (<a> Hx))
        (have <c> (elem x (emptyset T)) :by (<b> (elem x (emptyset T)))))
      (have <d> (subset s (emptyset T)) :by <c>)
      (have <e> p/absurd :by (Hne <d>)))
    (have <f> _ :by ((classic/not-not-impl (exists [x T] (elem x s))) <e>)))
  (qed <f>))

(definition psubset
  "The anti-reflexive variant of the subset relation.

The expression `(psubset T s1 s2)` means that
 the set `s1` is a subset of `s2`, but that the two
sets are distinct, i.e. `s1`⊂`s2` (or more explicitely `s1`⊊`s2`)."
  [?T :type, [s1 s2 (set T)]]
  (and (subset s1 s2)
       (not (seteq s1 s2))))

(defthm psubset-antirefl
  [?T :type, s (set T)]
  (not (psubset s s)))

(proof 'psubset-antirefl-thm
  (assume [H (psubset s s)]
    (have <a> (not (seteq s s))
          :by (p/and-elim-right H))
    (have <b> (seteq s s) :by (seteq-refl s))
    (have <c> p/absurd :by (<a> <b>)))
  (qed <c>))

(defthm psubset-antisym
  [?T :type, [s1 s2 (set T)]]
  (not (and (psubset s1 s2)
            (psubset s2 s1))))

(proof 'psubset-antisym-thm
  (assume [H (and (psubset s1 s2)
                  (psubset s2 s1))]
    (have <a> (not (seteq s1 s2))
          :by (p/and-elim-right (p/and-elim-left H)))
    (have <b> (subset s1 s2)
          :by (p/and-elim-left (p/and-elim-left H)))
    (have <c> (subset s2 s1)
          :by (p/and-elim-left (p/and-elim-right H)))
    (have <d> (seteq s1 s2)
          :by (p/and-intro <b> <c>))
    (have <e> p/absurd :by (<a> <d>)))
  (qed <e>))

(defthm psubset-trans
  "The proper subset relation is transitive."
  [?T :type, [s1 s2 s3 (set T)]]
  (==> (psubset s1 s2)
       (psubset s2 s3)
       (psubset s1 s3)))

(proof 'psubset-trans-thm
  (assume [H1 (psubset s1 s2)
           H2 (psubset s2 s3)]
    (have <a> (subset s1 s3)
          :by ((subset-trans s1 s2 s3)
               (p/and-elim-left H1)
               (p/and-elim-left H2)))
    (assume [H (seteq s1 s3)]
      (have <b> (set-equal s1 s3)
            :by ((seteq-implies-set-equal s1 s3)
                 H))
      (have <c> (psubset s3 s2)
            :by ((set-equal-prop s1 s3 (lambda [x (set T)]
                                         (psubset x s2)))
                 <b> H1))
      (have <d> p/absurd
            :by ((psubset-antisym s2 s3)
                 (p/and-intro H2 <c>))))
    (have <e> _ :by (p/and-intro <a> <d>)))
  (qed <e>))

(defthm psubset-emptyset
  [?T :type, s (set T)]
  (==> (psubset (emptyset T) s)
       (not (seteq s (emptyset T)))))

(proof 'psubset-emptyset-thm
  (assume [H (psubset (emptyset T) s)]
    (assume [H' (seteq s (emptyset T))]
      (have <a> (not (seteq (emptyset T) s))
            :by (p/and-elim-right H))
      (have <b> (seteq (emptyset T) s)
            :by ((seteq-sym s (emptyset T)) H'))
      (have <c> p/absurd :by (<a> <b>))))
  (qed <c>))

(defthm psubset-emptyset-conv
  [?T :type, s (set T)]
  (==> (not (seteq s (emptyset T)))
       (psubset (emptyset T) s)))

(proof 'psubset-emptyset-conv-thm
  (assume [H (not (seteq s (emptyset T)))]
    (have <a> (subset (emptyset T) s)
          :by (subset-emptyset-lower-bound s))
    (assume [H' (seteq (emptyset T) s)]
      (have <b> (seteq s (emptyset T))
            :by ((seteq-sym (emptyset T) s) H'))
      (have <c> p/absurd :by (H <b>)))
    (have <d> (psubset (emptyset T) s)
          :by (p/and-intro <a> <c>)))
  (qed <d>))

(defthm psubset-emptyset-equiv
  [?T :type, s (set T)]
  (<=> (psubset (emptyset T) s)
       (not (seteq s (emptyset T)))))

(proof 'psubset-emptyset-equiv-thm
  (qed (p/and-intro (psubset-emptyset s)
                    (psubset-emptyset-conv s))))


(definition insert
  "Insert element `e` in set `s`."
  [[?T :type] [e T] [s (set T)]]
  (lambda [x T]
    (or (equal x e)
        (elem x s))))

(defthm insert-elem
  [[?T :type] [e T] [s (set T)]]
  (elem e (insert e s)))

(proof 'insert-elem-thm
  (have <a> (equal e e) :by (eq/eq-refl e))
  (qed (p/or-intro-left <a> (elem e s))))


(defthm insert-elem-alt
  [[?T :type] [e T] [s (set T)]]
  (forall [x T] 
    (==> (elem x s)
         (elem x (insert e s)))))

(proof 'insert-elem-alt-thm
  (assume [x _
           Hx _]
    (have <a> _ :by (p/or-intro-right (equal x e) Hx)))
  (qed <a>))

(definition remove
  "Remove element `e` of set `s`."
  [[?T :type] [e T] [s (set T)]]
  (lambda [x T]
    (and (not (equal x e))
         (elem x s))))

(defthm remove-not-elem
  [[?T :type] [e T] [s (set T)]]
  (not (elem e (remove e s))))

(proof 'remove-not-elem-thm
  (assume [Hcontra (elem e (remove e s))]
    (have <a> (not (equal e e)) :by (p/and-elim-left Hcontra))
    (have <b> p/absurd :by (<a> (eq/eq-refl e))))
  (qed <b>))




