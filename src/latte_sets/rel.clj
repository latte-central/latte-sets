(ns latte-sets.rel
  "A **relation** from elements of
a given type `T` to elements of `U` is formalized with type `(==> T U :type)`.

  This namespace provides some important properties about such
  relations."

  (:refer-clojure :exclude [and or not identity set])

  (:require [latte.core :as latte :refer [definition defaxiom defthm defimplicit
                                          deflemma forall lambda
                                          proof assume have pose qed]]
            [latte.utils :as u]
            [latte-prelude.prop :as p :refer [and and* or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.fun :as fun]
            [latte-sets.set :as sets :refer [set set-of elem]]))

(definition rel
  "The type of relations."
  [T :type, U :type]
  (==> T U :type))

(defn fetch-rel-type [def-env ctx r-type]
  "Fetch the `T` and `U` in a relation-type `r-type` of the form `(rel T U)` (fails otherwise).
This function is used for implicits in relations."
  (let [[T cod-type] (p/decompose-impl-type def-env ctx r-type)]
    (let [[U _] (p/decompose-impl-type def-env ctx cod-type)]
      [T U])))

(u/register-implicit-type-parameters-handler! 'rel fetch-rel-type 2)

(definition dom
  "The domain of relation `R`."
  [[?T ?U :type] [R (rel T U)]]
  (set-of [x T]
          (exists [y U] (R x y))))

(definition ran
  "The range of relation `R`."
  [[?T ?U :type] [R (rel T U)]]
  (set-of [y U]
          (exists [x T] (R x y))))

(definition identity
  "The indentity relation on `T`."
  [[T :type]]
  (lambda [x y T]
    (equal x y)))

(definition reflexive
  "A reflexive relation."
  [?T :type, R (rel T T)]
  (forall [x T] (R x x)))

(defthm ident-refl
  [T :type]
  (reflexive (identity T)))

(proof 'ident-refl
  (assume [x T]
    (have <a> (equal x x) :by (eq/eq-refl x)))
  (qed <a>))

(definition refl-closure
  "The reflexive closure of relation `R`."
  [?T :type, R (rel T T)]
  (lambda [x y T]
    (or (R x y)
        (equal x y))))

(defthm reflexive-refl-closure
  [?T :type, R (rel T T)]
  (reflexive (refl-closure R)))

(proof 'reflexive-refl-closure-thm
  (assume [x T]
    (have <a> _ :by (p/or-intro-right (R x x) (eq/eq-refl x))))
  (qed <a>))

(definition symmetric
  "A symmetric relation."
  [?T :type, R (rel T T)]
  (forall [x y T]
    (==> (R x y)
         (R y x))))

(defthm ident-sym
  [T :type]
  (symmetric (identity T)))

(proof 'ident-sym
  (assume [x T
           y T
           Hx ((identity T) x y)]
    (have <a> (equal x y) :by Hx)
    (have <b> (equal y x) :by (eq/eq-sym <a>)))
  (qed <b>))

(definition symm-closure
  "The symmetric closure of relation `R`."
  [?T :type, R (rel T T)]
  (lambda [x y T]
    (or (R x y)
        (R y x))))

(defthm symmetric-symm-closure
  [?T :type, R (rel T T)]
  (symmetric (symm-closure R)))

(proof 'symmetric-symm-closure-thm
  (pose R* := (symm-closure R))
  (assume [x T y T
           H (R* x y)]
    (assume [Hxy (R x y)]
      (have <a> (R* y x) :by (p/or-intro-right (R y x) Hxy)))
    (assume [Hyx (R y x)]
      (have <b> (R* y x) :by (p/or-intro-left Hyx (R x y))))
    (have <c> (R* y x) :by (p/or-elim H <a> <b>)))
  (qed <c>))

(definition transitive
  "A transitive relation."
  [?T :type, R (rel T T)]
  (forall [x y z T]
    (==> (R x y)
         (R y z)
         (R x z))))

;; remark : we cannot define the transitive clojure now
;; because we need a fixed point definition
;; It is thus defined in powerrel.

(defthm ident-trans
  [T :type]
  (transitive (identity T)))

(proof 'ident-trans
  (assume [x T
           y T
           z T
           H1 ((identity T) x y)
           H2 ((identity T) y z)]
    (have <a> (equal x y) :by H1)
    (have <b> (equal y z) :by H2)
    (have <c> (equal x z) :by (eq/eq-trans <a> <b>)))
  (qed <c>))

(definition equivalence
  "An equivalence relation."
  [?T :type, R (rel T T)]
  (and* (reflexive R)
        (symmetric R)
        (transitive R)))

(defthm ident-equiv
  "The indentity on `T` is an equivalence relation."
  [T :type]
  (equivalence (identity T)))

(proof 'ident-equiv
  (qed (p/and-intro* (ident-refl T)
                     (ident-sym T)
                     (ident-trans T))))

(definition fullrel
  "The full (total) relation between `T` and `U`."
  [T :type, U :type]
  (lambda [x T]
    (lambda [y U] p/truth)))

(defthm fullrel-prop
  [T :type, U :type]
  (forall [x T]
    (forall [y U]
      ((fullrel T U) x y))))

(proof 'fullrel-prop
  (assume [x T
           y U]
    (have <a> ((fullrel T U) x y) :by p/truth-is-true))
  (qed <a>))

(definition emptyrel
  "The empty relation."
  [T :type, U :type]
  (lambda [x T]
    (lambda [y U]
      p/absurd)))

(defthm emptyrel-prop
  [T :type, U :type]
  (forall [x T]
    (forall [y U]
      (not ((emptyrel T U) x y)))))

(proof 'emptyrel-prop
  (assume [x T
           y U
           H ((emptyrel T U) x y)]
    (have <a> p/absurd :by H))
  (qed <a>))

(definition subrel
  "The subset ordering for relations, i.e. `R1`⊆`R2`"
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (forall [x T]
    (forall [y U]
      (==> (R1 x y)
           (R2 x y)))))

(defthm subrel-refl
  [[?T ?U :type] [R (rel T U)]]
  (subrel R R))

(proof 'subrel-refl-thm
  (assume [x T
           y U
           H1 (R x y)]
    (have <a> (R x y) :by H1))
  (qed <a>))

(defthm subrel-trans
  [[?T ?U :type] [R1 R2 R3 (rel T U)]]
  (==> (subrel R1 R2)
       (subrel R2 R3)
       (subrel R1 R3)))

(proof 'subrel-trans-thm
  (assume [H1 (subrel R1 R2)
           H2 (subrel R2 R3)]
    (assume [x T
             y U]
      (have <a> (==> (R1 x y) (R2 x y)) :by (H1 x y))
      (have <b> (==> (R2 x y) (R3 x y)) :by (H2 x y))
      (have <c> (==> (R1 x y) (R3 x y))
            :by (p/impl-trans <a> <b>))))
  (qed <c>))

(defthm subrel-prop
  "Preservation of properties on relational subsets."
  [[?T ?U :type], P (==> T U :type), [R1 R2 (rel T U)]]
  (==> (forall [x T]
         (forall [y U]
           (==> (R2 x y)
                (P x y))))
       (subrel R1 R2)
       (forall [x T]
         (forall [y U]
           (==> (R1 x y)
                (P x y))))))

(proof 'subrel-prop-thm
  (assume [H1 (forall [x T]
                      (forall [y U]
                              (==> (R2 x y)
                                   (P x y))))
           H2 (subrel R1 R2)]
    (assume [x T
             y U
             Hxy (R1 x y)]
      (have <a> (R2 x y) :by (H2 x y Hxy))
      (have <b> (P x y) :by (H1 x y <a>))))
  (qed <b>))

(defthm subrel-emptyrel-lower-bound
  "The empty relation is a subset of every other relations."
  [[?T ?U :type] [R (rel T U)]]
  (subrel (emptyrel T U) R))

(proof 'subrel-emptyrel-lower-bound-thm
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <a> p/absurd :by Hxy)
    (have <b> (R x y) :by (<a> (R x y))))
  (qed <b>))

(defthm subrel-fullrel-upper-bound
  "The full relation is a superset of every other relations."
  [[?T ?U :type] [R (rel T U)]]
  (subrel R (fullrel T U)))

(proof 'subrel-fullrel-upper-bound-thm
  (assume [x T
           y U
           Hxy (R x y)]
    (have <a> ((fullrel T U) x y)
          :by p/truth-is-true))
  (qed <a>))


(defthm refl-closure-sub
  [?T :type, R (rel T T)]
  (subrel R (refl-closure R)))

(proof 'refl-closure-sub-thm
  (assume [x T y T
           HR (R x y)]
    (have <a> (or (R x y) (equal x y))
          :by (p/or-intro-left HR (equal x y))))
  (qed <a>))

(defthm refl-closure-smallest
  [?T :type, R (rel T T)]
  (forall [S (rel T T)]
    (==> (subrel R S)
         (reflexive S)
         (subrel (refl-closure R) S))))

(proof 'refl-closure-smallest-thm
  (pose R* := (refl-closure R))
  (assume [S (rel T T)
           Hsub (subrel R S)
           HSrefl (reflexive S)]
    (assume [x T y T
             HR* (R* x y)]
      (assume [HR*1 (R x y)]
        (have <a> (S x y) :by (Hsub x y HR*1)))
      (assume [HR*2 (equal x y)]
        (have <b1> (S x x) :by (HSrefl x))
        (have <b> (S x y) :by (eq/nrewrite 2 <b1> HR*2)))
      (have <c> (S x y) :by (p/or-elim HR* <a> <b>))))
  (qed <c>))

(defthm symm-closure-sub
  [?T :type, R (rel T T)]
  (subrel R (symm-closure R)))

(proof 'symm-closure-sub-thm
  (assume [x T y T
           HR (R x y)]
    (have <a> (or (R x y) (R y x))
          :by (p/or-intro-left HR (R y x))))
  (qed <a>))

(defthm symm-closure-smallest
  [?T :type, R (rel T T)]
  (forall [S (rel T T)]
    (==> (subrel R S)
         (symmetric S)
         (subrel (symm-closure R) S))))

(proof 'symm-closure-smallest-thm
  (pose R* := (symm-closure R))
  (assume [S (rel T T)
           Hsub (subrel R S)
           HSsym (symmetric S)]
    (assume [x T y T
             HR* (R* x y)]
      (assume [HR*1 (R x y)]
        (have <a> (S x y) :by (Hsub x y HR*1)))
      (assume [HR*2 (R y x)]
        (have <b1> (S y x) :by (Hsub y x HR*2))
        (have <b> (S x y) :by (HSsym y x <b1>)))
      (have <c> (S x y) :by (p/or-elim HR* <a> <b>))))
  (qed <c>))

(definition releq
  "Subset-based equality on relations."
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (and (subrel R1 R2)
       (subrel R2 R1)))

(defthm releq-refl
  [[?T ?U :type] [R (rel T U)]]
  (releq R R))

(proof 'releq-refl-thm
  (have <a> (subrel R R) :by (subrel-refl R))
  (qed (p/and-intro <a> <a>)))

(defthm releq-sym
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (==> (releq R1 R2)
       (releq R2 R1)))

(proof 'releq-sym-thm
  (assume [H (releq R1 R2)]
    (have <a> _ :by (p/and-intro (p/and-elim-right H)
                                 (p/and-elim-left H))))
  (qed <a>))

(defthm releq-trans
  [[?T ?U :type] [R1 R2 R3 (rel T U)]]
  (==> (releq R1 R2)
       (releq R2 R3)
       (releq R1 R3)))

(proof 'releq-trans-thm
  (assume [H1 (releq R1 R2)
           H2 (releq R2 R3)]
    (have <a> (subrel R1 R2) :by (p/and-elim-left H1))
    (have <b> (subrel R2 R3) :by (p/and-elim-left H2))
    (have <c> (subrel R1 R3) :by ((subrel-trans R1 R2 R3) <a> <b>))
    (have <d> (subrel R3 R2) :by (p/and-elim-right H2))
    (have <e> (subrel R2 R1) :by (p/and-elim-right H1))
    (have <f> (subrel R3 R1) :by ((subrel-trans R3 R2 R1) <d> <e>))
    (have <g> _ :by (p/and-intro <c> <f>)))
  (qed <g>))

(definition rel-equal
  "A *Leibniz*-stype equality for relations.

It says that two relations `R1` and `R2` are equal iff for
any predicate `P` then `(P R1)` if and only if `(P R2)`.

Note that the identification with [[seteq]] is non-trivial,
 and requires an axiom."
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (forall [P (==> (rel T U) :type)]
          (<=> (P R1) (P R2))))

(defthm rel-equal-prop
  [[?T ?U :type] [R1 R2 (rel T U)], P (==> (rel T U) :type)]
  (==> (rel-equal R1 R2)
       (P R1)
       (P R2)))

(proof 'rel-equal-prop-thm
  (assume [H (rel-equal R1 R2)
           HR1 (P R1)]
    (have <a> (<=> (P R1) (P R2))
          :by (H P))
    (have <b> (==> (P R1) (P R2))
          :by (p/and-elim-left <a>))
    (have <c> (P R2) :by (<b> HR1)))
  (qed <c>))

(defthm rel-equal-refl
  [[?T ?U :type] [R (rel T U)]]
  (rel-equal R R))

(proof 'rel-equal-refl-thm
  (assume [P (==> (rel T U) :type)]
    (assume [H1 (P R)]
      (have <a> (P R) :by H1))
    (have <b> _ :by (p/and-intro <a> <a>)))
  (qed <b>))

(defthm rel-equal-sym
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (==> (rel-equal R1 R2)
       (rel-equal R2 R1)))

(proof 'rel-equal-sym-thm
  (assume [H (rel-equal R1 R2)]
    (assume [P (==> (rel T U) :type)]
      (assume [H1 (P R2)]
        (have <a> (==> (P R2) (P R1))
              :by (p/and-elim-right (H P)))
        (have <b> (P R1) :by (<a> H1)))
      (assume [H2 (P R1)]
        (have <c> (==> (P R1) (P R2))
              :by (p/and-elim-left (H P)))
        (have <d> (P R2) :by (<c> H2)))
      (have <e> _ :by (p/and-intro <b> <d>))))
  (qed <e>))

(defthm rel-equal-trans
  [[?T ?U :type] [R1 R2 R3 (rel T U)]]
  (==> (rel-equal R1 R2)
       (rel-equal R2 R3)
       (rel-equal R1 R3)))

(proof 'rel-equal-trans-thm
  (assume [H1 (rel-equal R1 R2)
           H2 (rel-equal R2 R3)]
    (assume [P (==> (rel T U) :type)]
      (assume [H3 (P R1)]
        (have <a> (==> (P R1) (P R2))
              :by (p/and-elim-left (H1 P)))
        (have <b> (P R2) :by (<a> H3))
        (have <c> (==> (P R2) (P R3))
              :by (p/and-elim-left (H2 P)))
        (have <d> (P R3) :by (<c> <b>)))
      (assume [H4 (P R3)]
        (have <e> (==> (P R3) (P R2))
              :by (p/and-elim-right (H2 P)))
        (have <f> (P R2) :by (<e> H4))
        (have <g> (==> (P R2) (P R1))
              :by (p/and-elim-right (H1 P)))
        (have <h> (P R1) :by (<g> <f>)))
      (have <i> _ :by (p/and-intro <d> <h>))))
  (qed <i>))

(defthm rel-equal-implies-subrel
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (==> (rel-equal R1 R2)
       (subrel R1 R2)))

(proof 'rel-equal-implies-subrel-thm
  (assume [H (rel-equal R1 R2)
           x T
           y U]
    (pose Qxy := (lambda [R (rel T U)]
                   (R x y)))
    (have <a> (<=> (R1 x y) (R2 x y))
          :by (H Qxy))
    (have <b> (==> (R1 x y) (R2 x y))
          :by (p/and-elim-left <a>)))
  (qed <b>))

(defthm rel-equal-implies-releq
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (==> (rel-equal R1 R2)
       (releq R1 R2)))

(proof 'rel-equal-implies-releq-thm
  (assume [H (rel-equal R1 R2)]
    (have <a> (subrel R1 R2)
          :by ((rel-equal-implies-subrel R1 R2) H))
    (have <b> (rel-equal R2 R1)
          :by ((rel-equal-sym R1 R2) H))
    (have <c> (subrel R2 R1)
          :by ((rel-equal-implies-subrel R2 R1) <b>))
    (have <d> _ :by (p/and-intro <a> <c>)))
  (qed <d>))

(defaxiom releq-implies-rel-equal
  "As for the set case (cf. [[sets/seteq-implies-set-equal]]),
going from the subset-based equality to the (thus more general) *leibniz*-style
one requires an axiom."
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (==> (releq R1 R2)
       (rel-equal R1 R2)))

(defthm rel-equal-releq
  "Coincidence of *Leibniz*-style and subset-based equality for relations."
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (<=> (rel-equal R1 R2)
       (releq R1 R2)))

(proof 'rel-equal-releq-thm
  (qed (p/and-intro (rel-equal-implies-releq R1 R2)
                    (releq-implies-rel-equal R1 R2))))

(definition rcomp
  "Sequential relational composition."
  [[?T ?U ?V :type], R1 (rel T U), R2 (rel U V)]
  (lambda [x T]
    (lambda [z V]
      (exists [y U]
        (and (R1 x y) (R2 y z))))))

(deflemma rcomp-assoc-subrel-aux
  [[T U V W :type], R1 (rel T U), R2 (rel U V), R3 (rel V W), x T, z W]
  (==> ((rcomp R1 (rcomp R2 R3)) x z)
       ((rcomp (rcomp R1 R2) R3) x z)))

(proof 'rcomp-assoc-subrel-aux
  (assume [H ((rcomp R1 (rcomp R2 R3)) x z)]
    (have <a> (exists [y U]
                (and (R1 x y) ((rcomp R2 R3) y z))) :by H)
    (assume [y U
             Hy (and (R1 x y) ((rcomp R2 R3) y z))]
      (have <b> (exists [t V]
                  (and (R2 y t) (R3 t z))) :by (p/and-elim-right Hy))
      (assume [t V
               Ht (and (R2 y t) (R3 t z))]
        (have <c> (and (R1 x y) (R2 y t))
              :by (p/and-intro (p/and-elim-left Hy) (p/and-elim-left Ht)))
        (have <d> ((rcomp R1 R2) x t)
              :by ((q/ex-intro (lambda [k U]
                                       (and (R1 x k) (R2 k t))) y) <c>))
        (have <e> (R3 t z) :by (p/and-elim-right Ht))
        (have <f> _ :by (p/and-intro <d> <e>))
        (have <g> ((rcomp (rcomp R1 R2) R3) x z)
              :by ((q/ex-intro (lambda [k V]
                                       (and ((rcomp R1 R2) x k)
                                            (R3 k z))) t) <f>)))
      (have <h> _ :by (q/ex-elim <b> <g>)))
    (have <i> _ :by (q/ex-elim <a> <h>)))
  (qed <i>))

(defthm rcomp-assoc-subrel
  [[?T ?U ?V ?W :type], R1 (rel T U), R2 (rel U V), R3 (rel V W)]
  (subrel (rcomp R1 (rcomp R2 R3))
          (rcomp (rcomp R1 R2) R3)))

(proof 'rcomp-assoc-subrel-thm
  (assume [x T
           y W
           H ((rcomp R1 (rcomp R2 R3)) x y)]
    (have <a> ((rcomp (rcomp R1 R2) R3) x y)
          :by ((rcomp-assoc-subrel-aux
                T U V W R1 R2 R3)
               x y H)))
  (qed <a>))

(deflemma rcomp-assoc-suprel-aux
  [[T U V W :type] [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)] [x T] [z W]]
  (==> ((rcomp (rcomp R1 R2) R3) x z)
       ((rcomp R1 (rcomp R2 R3)) x z)))

(proof 'rcomp-assoc-suprel-aux
  (assume [H ((rcomp (rcomp R1 R2) R3) x z)]
    (have <a> (exists [y V]
                (and ((rcomp R1 R2) x y)
                     (R3 y z))) :by H)
    (assume [y V
             Hy (and ((rcomp R1 R2) x y)
                     (R3 y z))]
      (have <b> (exists [t U] (and (R1 x t) (R2 t y)))
            :by (p/and-elim-left Hy))
      (assume [t U
               Ht (and (R1 x t) (R2 t y))]
        (have <c1> (R1 x t) :by (p/and-elim-left Ht))
        (have <c2> (and (R2 t y) (R3 y z))
              :by (p/and-intro (p/and-elim-right Ht)
                               (p/and-elim-right Hy)))
        (have <c3> ((rcomp R2 R3) t z)
              :by ((q/ex-intro (lambda [k V]
                                       (and (R2 t k) (R3 k z))) y)
                   <c2>))
        (have <c> ((rcomp R1 (rcomp R2 R3)) x z)
              :by ((q/ex-intro (lambda [k U]
                                       (and (R1 x k)
                                            ((rcomp R2 R3) k z))) t)
                   (p/and-intro <c1> <c3>))))
      (have <d> _ :by (q/ex-elim <b> <c>)))
    (have <e> _ :by (q/ex-elim <a> <d>)))
  (qed <e>))

(defthm rcomp-assoc-suprel
  [[?T ?U ?V ?W :type], R1 (rel T U), R2 (rel U V), R3 (rel V W)]
  (subrel (rcomp (rcomp R1 R2) R3)
          (rcomp R1 (rcomp R2 R3))))

(proof 'rcomp-assoc-suprel-thm
  (assume [x T
           z W]
    (have <a> _ :by (rcomp-assoc-suprel-aux
                     T U V W
                     R1 R2 R3 x z)))
  (qed <a>))

(defthm rcomp-assoc
  "Relational composition is associative."
  [[?T ?U ?V ?W :type] [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)]]
  (releq (rcomp R1 (rcomp R2 R3))
         (rcomp (rcomp R1 R2) R3)))

(proof 'rcomp-assoc-thm
  (qed (p/and-intro (rcomp-assoc-subrel R1 R2 R3)
                    (rcomp-assoc-suprel R1 R2 R3))))

(definition psubrel
  "The anti-reflexive variant of [[subrel]]."
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (and (subrel R1 R2)
       (not (releq R1 R2))))

(defthm psubrel-antirefl
  [[?T ?U :type] [R (rel T U)]]
  (not (psubrel R R)))

(proof 'psubrel-antirefl-thm
  (assume [H (psubrel R R)]
    (have <a> (not (releq R R))
          :by (p/and-elim-right H))
    (have <b> p/absurd :by (<a> (releq-refl R))))
  (qed <b>))

(defthm psubrel-antisym
  [[?T ?U :type] [R1 R2 (rel T U)]]
  (not (and (psubrel R1 R2)
            (psubrel R2 R1))))

(proof 'psubrel-antisym-thm
  (assume [H (and (psubrel R1 R2)
                  (psubrel R2 R1))]
    (have <a> (not (releq R1 R2))
          :by (p/and-elim-right (p/and-elim-left H)))
    (have <b> (releq R1 R2)
          :by (p/and-intro (p/and-elim-left (p/and-elim-left H))
                           (p/and-elim-left (p/and-elim-right H))))
    (have <c> p/absurd :by (<a> <b>)))
  (qed <c>))

(defthm psubrel-trans
  [[?T ?U :type] [R1 R2 R3 (rel T U)]]
  (==> (psubrel R1 R2)
       (psubrel R2 R3)
       (psubrel R1 R3)))

(proof 'psubrel-trans-thm
  (assume [H1 (psubrel R1 R2)
           H2 (psubrel R2 R3)]
    (have <a> (subrel R1 R3)
          :by ((subrel-trans R1 R2 R3)
               (p/and-elim-left H1)
               (p/and-elim-left H2)))
    (assume [H3 (releq R1 R3)]
      (have <b> (rel-equal R1 R3)
            :by ((releq-implies-rel-equal R1 R3)
                 H3))
      (have <c> (psubrel R3 R2)
            :by ((rel-equal-prop R1 R3 (lambda [R (rel T U)]
                                         (psubrel R R2)))
                 <b> H1))
      (have <d> p/absurd :by ((psubrel-antisym R2 R3)
                              (p/and-intro H2 <c>))))
    (have <e> _ :by (p/and-intro <a> <d>)))
  (qed <e>))

(defthm psubrel-emptyrel
  [[?T ?U :type] [R (rel T U)]]
  (==> (psubrel (emptyrel T U) R)
       (not (releq R (emptyrel T U)))))

(proof 'psubrel-emptyrel-thm
  (assume [H (psubrel (emptyrel T U) R)]
    (assume [H' (releq R (emptyrel T U))]
      (have <a> (not (releq (emptyrel T U) R))
            :by (p/and-elim-right H))
      (have <b> (releq  (emptyrel T U) R)
            :by ((releq-sym R (emptyrel T U)) H'))
      (have <c> p/absurd :by (<a> <b>))))
  (qed <c>))

(defthm psubrel-emptyrel-conv
  [[?T ?U :type] [R (rel T U)]]
  (==> (not (releq R (emptyrel T U)))
       (psubrel (emptyrel T U) R)))

(proof 'psubrel-emptyrel-conv-thm
  (assume [H (not (releq R (emptyrel T U)))]
    (have <a> (subrel (emptyrel T U) R)
          :by (subrel-emptyrel-lower-bound R))
    (assume [H' (releq (emptyrel T U) R)]
      (have <b> (releq R (emptyrel T U))
            :by ((releq-sym (emptyrel T U) R) H'))
      (have <c> p/absurd :by (H <b>)))
    (have <d> (psubrel (emptyrel T U) R)
          :by (p/and-intro <a> <c>)))
  (qed <d>))

(defthm psubrel-emptyrel-equiv
  [[?T ?U :type] [R (rel T U)]]
  (<=> (psubrel (emptyrel T U) R)
       (not (releq R (emptyrel T U)))))

(proof 'psubrel-emptyrel-equiv-thm
  (qed (p/and-intro (psubrel-emptyrel R)
                    (psubrel-emptyrel-conv R))))

(definition prod
  "The cartersian product of sets `s1` and `s2`, i.e. `s1`⨯`s2`."
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (lambda [x T]
    (lambda [y U]
      (and (elem x s1)
           (elem y s2)))))

(definition funrel
  "The relation corresponding to function `f`."
  [[?T ?U :type] [f (==> T U)]]
  (lambda [x T]
    (lambda [y U]
      (equal (f x) y))))

(definition functional
  [[?T ?U :type] [R (rel T U)]]
  (forall [x T]
    (q/unique (lambda [y U] (R x y)))))

(defthm funrel-functional
  [[?T ?U :type] [f (==> T U)]]
  (functional (funrel f)))

(proof 'funrel-functional-thm
  (pose R := (funrel f))
  (assume [x T]
    (have <a1> (equal (f x) (f x)) :by (eq/eq-refl (f x)))
    (have <a> (exists [y U] (R x y))
          :by ((q/ex-intro (lambda [y U] (R x y)) (f x)) <a1>))
    (assume [y1 U
             y2 U
             Hy1 (R x y1)
             Hy2 (R x y2)]
      (have <b1> (equal (f x) y1) :by Hy1)
      (have <b2> (equal (f x) y2) :by Hy2)
      (have <b> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym <b1>)
                                               <b2>)))
    (have <c> (q/unique (lambda [y U] (R x y)))
          :by (p/and-intro <a> <b>)))
  (qed <c>))

(definition relfun
  "The function corresponding to a total, functional relation."
  [[?T ?U :type] [R (rel T U)] [fproof (functional R)]]
  (lambda [x T] (q/the (fproof x))))

(defthm relfun-img-prop
  "The property of the relational/functional image."
  [[?T ?U :type] [R (rel T U)] [fproof (functional R)]]
  (forall [x T] (R x ((relfun R fproof) x))))

(proof 'relfun-img-prop-thm
  (assume [x T]
    (have <a> _ :by (q/the-prop (fproof x))))
  (qed <a>))

(defthm relfun-img
  "The image of a functional relation"
  [[?T ?U :type] [R (rel T U)] [fproof (functional R)]]
  (forall [x T]
    (forall [y U]
      (==> (R x y)
           (equal ((relfun R fproof) x) y)))))

(proof 'relfun-img-thm
  (assume [x T y U
           H (R x y)]
    (pose yy := (q/the (fproof x)))
    (have <a> (equal ((relfun R fproof) x) yy)
          :by (eq/eq-refl ((relfun R fproof) x)))
    (have <b> (equal y yy) :by ((q/the-lemma (fproof x)) y H))
    (have <c> (equal ((relfun R fproof) x) y)
          :by (eq/eq-trans <a> (eq/eq-sym <b>))))
  (qed <c>))

(defthm relfunrel-ext-equal
  "This is the extensional equality of a function `f` and
its relational characterization."
  [[?T ?U :type] [f (==> T U)]]
  (forall [x T]
    (equal (f x) ((relfun (funrel f) (funrel-functional f)) x))))

(proof 'relfunrel-ext-equal-thm
  (pose R := (funrel f))
  (pose fproof := (funrel-functional f))
  (assume [x T]
    (have <a> (R x (f x)) :by (eq/eq-refl (f x)))
    (have <b> (R x (q/the (fproof x)))
          :by (q/the-prop (fproof x)))
    (have <c> (equal (f x) (q/the (fproof x)))
          :by ((p/and-elim-right (fproof x))
               (f x)
               (q/the (fproof x))
               <a> <b>)))
  (qed <c>))

(defthm relfunrel-equal
  "This is the intentional variant of [[relfunrel-ext-equal]]."
  [[?T ?U :type] [f (==> T U)]]
  (equal f (relfun (funrel f) (funrel-functional f))))

(proof 'relfunrel-equal-thm
  (qed ((fun/functional-extensionality
         f
         (relfun (funrel f) (funrel-functional f)))
        (relfunrel-ext-equal f))))
