(ns latte-sets.rel
  "A **relation** from elements of
a given type `T` to elements of `U` is formalized with type `(==> T U :type)`.

  This namespace provides some important properties about such
  relations."

  (:refer-clojure :exclude [and or not identity])

  (:require [latte.core :as latte :refer [definition defaxiom defthm
                                          deflemma forall lambda ==>
                                          proof assume have]]
            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]))

(definition rel
  "The type of relations."
  [[T :type] [U :type]]
  (==> T U :type))

(definition dom
  "The domain of relation `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [x T]
    (exists [y U] (R x y))))

(definition ran
  "The range of relation `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [y U]
          (exists [x T] (R x y))))

(definition identity
  "The indentity relation on `T`."
  [[T :type]]
  (lambda [x y T]
    (equal T x y)))

(definition reflexive
  "A reflexive relation."
  [[T :type] [R (rel T T)]]
  (forall [x T] (R x x)))

(defthm ident-refl
  [[T :type]]
  (reflexive T (identity T)))

(proof ident-refl
    :script
  (assume [x T]
    (have <a> (equal T x x) :by (eq/eq-refl T x)))
  (qed <a>))

(definition symmetric
  "A symmetric relation."
  [[T :type] [R (rel T T)]]
  (forall [x y T]
    (==> (R x y)
         (R y x))))

(defthm ident-sym
  [[T :type]]
  (symmetric T (identity T)))

(proof ident-sym
    :script
  (assume [x T
           y T
           Hx ((identity T) x y)]
    (have <a> (equal T x y) :by Hx)
    (have <b> (equal T y x) :by (eq/eq-sym% <a>))
    (qed <b>)))

(definition transitive
  "A transitive relation."
  [[T :type] [R (rel T T)]]
  (forall [x y z T]
    (==> (R x y)
         (R y z)
         (R x z))))

(defthm ident-trans
  [[T :type]]
  (transitive T (identity T)))

(proof ident-trans
    :script
  (assume [x T
           y T
           z T
           H1 ((identity T) x y)
           H2 ((identity T) y z)]
    (have <a> (equal T x y) :by H1)
    (have <b> (equal T y z) :by H2)
    (have <c> (equal T x z) :by (eq/eq-trans% <a> <b>))
    (qed <c>)))

(definition equivalence
  "An equivalence relation."
  [[T :type] [R (rel T T)]]
  (and (reflexive T R)
       (and (symmetric T R)
            (transitive T R))))

(defthm ident-equiv
  "The indentity on `T` is an equivalence relation."
  [[T :type]]
  (equivalence T (identity T)))

(proof ident-equiv
    :script
  (have <a> _ :by (p/and-intro% (ident-refl T)
                                (p/and-intro% (ident-sym T)
                                              (ident-trans T))))
  (qed <a>))


(definition fullrel
  "The full (total) relation between `T` and `U`."
  [[T :type] [U :type]]
  (lambda [x T]
    (lambda [y U] p/truth)))

(defthm fullrel-prop
  [[T :type] [U :type]]
  (forall [x T]
    (forall [y U]
      ((fullrel T U) x y))))

(proof fullrel-prop
    :script
  (assume [x T
           y U]
    (have <a> ((fullrel T U) x y) :by p/truth-is-true)
    (qed <a>)))

(definition emptyrel
  "The empty relation."
  [[T :type] [U :type]]
  (lambda [x T]
    (lambda [y U]
      p/absurd)))

(defthm emptyrel-prop
  [[T :type] [U :type]]
  (forall [x T]
    (forall [y U]
      (not ((emptyrel T U) x y)))))

(proof emptyrel-prop
    :script
  (assume [x T
           y U
           H ((emptyrel T U) x y)]
    (have <a> p/absurd :by H)
    (qed <a>)))

(definition subrel
  "The subser ordering for relations."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (forall [x T]
    (forall [y U]
      (==> (R1 x y)
           (R2 x y)))))

(defthm subrel-refl
  [[T :type] [U :type] [R (rel T U)]]
  (subrel T U R R))

(proof subrel-refl
    :script
  (assume [x T
           y U
           H1 (R x y)]
    (have <a> (R x y) :by H1)
    (qed <a>)))

(defthm subrel-trans
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (==> (subrel T U R1 R2)
       (subrel T U R2 R3)
       (subrel T U R1 R3)))

(proof subrel-trans
    :script
  (assume [H1 (subrel T U R1 R2)
           H2 (subrel T U R2 R3)]
    (assume [x T
             y U]
      (have <a> (==> (R1 x y) (R2 x y)) :by (H1 x y))
      (have <b> (==> (R2 x y) (R3 x y)) :by (H2 x y))
      (have <c> (==> (R1 x y) (R3 x y))
            :by (p/impl-trans% <a> <b>))
      (qed <c>))))

(defthm subrel-prop
  "Preservation of properties on relational subsets."
  [[T :type] [U :type] [P (==> T U :type)][R1 (rel T U)] [R2 (rel T U)]]
  (==> (forall [x T]
         (forall [y U]
           (==> (R2 x y)
                (P x y))))
       (subrel T U R1 R2)
       (forall [x T]
         (forall [y U]
           (==> (R1 x y)
                (P x y))))))

(proof subrel-prop
    :script
  (assume [H1 (forall [x T]
         (forall [y U]
           (==> (R2 x y)
                (P x y))))
           H2 (subrel T U R1 R2)]
    (assume [x T
             y U
             Hxy (R1 x y)]
      (have <a> (R2 x y) :by (H2 x y Hxy))
      (have <b> (P x y) :by (H1 x y <a>)))
    (qed <b>)))

(defthm subrel-emptyrel-lower-bound
  "The empty relation is a subset of every other relations."
  [[T :type] [U :type] [R (rel T U)]]
  (subrel T U (emptyrel T U) R))

(proof subrel-emptyrel-lower-bound
    :script
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <a> p/absurd :by Hxy)
    (have <b> (R x y) :by (<a> (R x y)))
    (qed <b>)))

(defthm subrel-fullrel-upper-bound
  "The full relation is a superset of every other relations."
  [[T :type] [U :type] [R (rel T U)]]
  (subrel T U R (fullrel T U)))

(proof subrel-fullrel-upper-bound
    :script
  (assume [x T
           y U
           Hxy (R x y)]
    (have <a> ((fullrel T U) x y)
          :by p/truth-is-true)
    (qed <a>)))


(definition releq
  "Subset-based equality on relations."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (and (subrel T U R1 R2)
       (subrel T U R2 R1)))

(defthm releq-refl
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U R R))

(proof releq-refl
    :script
  (have <a> (subrel T U R R) :by (subrel-refl T U R))
  (have <b> _ :by (p/and-intro% <a> <a>))
  (qed <b>))

(defthm releq-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (==> (releq T U R1 R2)
       (releq T U R2 R1)))

(proof releq-sym
    :script
  (assume [H (releq T U R1 R2)]
    (have <a> _ :by (p/and-intro% (p/and-elim-right% H)
                                  (p/and-elim-left% H)))
    (qed <a>)))

(defthm releq-trans
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (==> (releq T U R1 R2)
       (releq T U R2 R3)
       (releq T U R1 R3)))

(proof releq-trans
    :script
  (assume [H1 (releq T U R1 R2)
           H2 (releq T U R2 R3)]
    (have <a> (subrel T U R1 R2) :by (p/and-elim-left% H1))
    (have <b> (subrel T U R2 R3) :by (p/and-elim-left% H2))
    (have <c> (subrel T U R1 R3) :by ((subrel-trans T U R1 R2 R3) <a> <b>))
    (have <d> (subrel T U R3 R2) :by (p/and-elim-right% H2))
    (have <e> (subrel T U R2 R1) :by (p/and-elim-right% H1))
    (have <f> (subrel T U R3 R1) :by ((subrel-trans T U R3 R2 R1) <d> <e>))
    (have <g> _ :by (p/and-intro% <c> <f>))
    (qed <g>)))

(definition rel-equal
  "A *Leibniz*-stype equality for relations.

It says that two relations `R1` and `R2` are equal iff for 
any predicate `P` then `(P R1)` if and only if `(P R2)`.

Note that the identification with [[seteq]] is non-trivial,
 and requires an axiom."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (forall [P (==> (rel T U) :type)]
    (<=> (P R1) (P R2))))

(defthm rel-equal-prop
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [P (==> (rel T U) :type)]]
  (==> (rel-equal T U R1 R2)
       (P R1)
       (P R2)))

(proof rel-equal-prop
    :script
  (assume [H (rel-equal T U R1 R2)
           HR1 (P R1)]
    (have <a> (<=> (P R1) (P R2))
          :by (H P))
    (have <b> (==> (P R1) (P R2))
          :by (p/and-elim-left% <a>))
    (have <c> (P R2) :by (<b> HR1))
    (qed <c>)))

(defthm rel-equal-refl
  [[T :type] [U :type] [R (rel T U)]]
  (rel-equal T U R R))

(proof rel-equal-refl
    :script
  (assume [P (==> (rel T U) :type)]
    (assume [H1 (P R)]
      (have <a> (P R) :by H1))
    (have <b> _ :by (p/and-intro% <a> <a>))
    (qed <b>)))

(defthm rel-equal-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (==> (rel-equal T U R1 R2)
       (rel-equal T U R2 R1)))

(proof rel-equal-sym
    :script
  (assume [H (rel-equal T U R1 R2)]
    (assume [P (==> (rel T U) :type)]
      (assume [H1 (P R2)]
        (have <a> (==> (P R2) (P R1))
              :by (p/and-elim-right% (H P)))
        (have <b> (P R1) :by (<a> H1)))
      (assume [H2 (P R1)]
        (have <c> (==> (P R1) (P R2))
              :by (p/and-elim-left% (H P)))
        (have <d> (P R2) :by (<c> H2)))
      (have <e> _ :by (p/and-intro% <b> <d>))
      (qed <e>))))

(defthm rel-equal-trans
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (==> (rel-equal T U R1 R2)
       (rel-equal T U R2 R3)
       (rel-equal T U R1 R3)))

(proof rel-equal-trans
    :script
  (assume [H1 (rel-equal T U R1 R2)
           H2 (rel-equal T U R2 R3)]
    (assume [P (==> (rel T U) :type)]
      (assume [H3 (P R1)]
        (have <a> (==> (P R1) (P R2))
              :by (p/and-elim-left% (H1 P)))
        (have <b> (P R2) :by (<a> H3))
        (have <c> (==> (P R2) (P R3))
              :by (p/and-elim-left% (H2 P)))
        (have <d> (P R3) :by (<c> <b>)))
      (assume [H4 (P R3)]
        (have <e> (==> (P R3) (P R2))
              :by (p/and-elim-right% (H2 P)))
        (have <f> (P R2) :by (<e> H4))
        (have <g> (==> (P R2) (P R1))
              :by (p/and-elim-right% (H1 P)))
        (have <h> (P R1) :by (<g> <f>)))
      (have <i> _ :by (p/and-intro% <d> <h>))
      (qed <i>))))

(defthm rel-equal-implies-subrel
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (==> (rel-equal T U R1 R2)
       (subrel T U R1 R2)))

(proof rel-equal-implies-subrel
    :script
  (assume [H (rel-equal T U R1 R2)
           x T
           y U]
    (pose Qxy := (lambda [R (rel T U)]
                   (R x y)))
    (have <a> (<=> (R1 x y) (R2 x y))
          :by (H Qxy))
    (have <b> (==> (R1 x y) (R2 x y))
          :by (p/and-elim-left% <a>))
    (qed <b>)))

(defthm rel-equal-implies-releq
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (==> (rel-equal T U R1 R2)
       (releq T U R1 R2)))

(proof rel-equal-implies-releq
    :script
  (assume [H (rel-equal T U R1 R2)]
    (have <a> (subrel T U R1 R2)
          :by ((rel-equal-implies-subrel T U R1 R2) H))
    (have <b> (rel-equal T U R2 R1)
          :by ((rel-equal-sym T U R1 R2) H))
    (have <c> (subrel T U R2 R1)
          :by ((rel-equal-implies-subrel T U R2 R1) <b>))
    (have <d> _ :by (p/and-intro% <a> <c>))
    (qed <d>)))

(defaxiom releq-implies-rel-equal-ax
  "As for the set case (cf. [[sets/seteq-implies-set-equal-ax]]),
going from the subset-based equality to the (thus more general) *leibniz*-style
one requires an axiom."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (==> (releq T U R1 R2)
       (rel-equal T U R1 R2)))

(defthm rel-equal-releq
  "Coincidence of *Leibniz*-style and subset-based equality for relations."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (<=> (rel-equal T U R1 R2)
       (releq T U R1 R2)))

(proof rel-equal-releq
    :script
  (have <a> _ :by (p/and-intro% (rel-equal-implies-releq T U R1 R2)
                                (releq-implies-rel-equal-ax T U R1 R2)))
  (qed <a>))

(definition rcomp
  "Sequential relational composition."
  [[T :type] [U :type] [V :type] [R1 (rel T U)] [R2 (rel U V)]]
  (lambda [x T]
    (lambda [z V]
      (exists [y U]
        (and (R1 x y) (R2 y z))))))


(deflemma rcomp-assoc-subrel-aux
  [[T :type] [U :type] [V :type] [W :type]
   [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)] [x T] [z W]]
  (==> ((rcomp T U W R1 (rcomp U V W R2 R3)) x z)
       ((rcomp T V W (rcomp T U V R1 R2) R3) x z)))

(proof rcomp-assoc-subrel-aux
    :script
  (assume [H ((rcomp T U W R1 (rcomp U V W R2 R3)) x z)]
    (have <a> (exists [y U]
                (and (R1 x y) ((rcomp U V W R2 R3) y z))) :by H)
    (assume [y U
             Hy (and (R1 x y) ((rcomp U V W R2 R3) y z))]
      (have <b> (exists [t V]
                  (and (R2 y t) (R3 t z))) :by (p/and-elim-right% Hy))
      (assume [t V
               Ht (and (R2 y t) (R3 t z))]
        (have <c> (and (R1 x y) (R2 y t))
              :by (p/and-intro% (p/and-elim-left% Hy) (p/and-elim-left% Ht)))
        (have <d> ((rcomp T U V R1 R2) x t)
              :by ((q/ex-intro U (lambda [k U]
                                   (and (R1 x k) (R2 k t))) y) <c>))
        (have <e> (R3 t z) :by (p/and-elim-right% Ht))
        (have <f> _ :by (p/and-intro% <d> <e>))
        (have <g> ((rcomp T V W (rcomp T U V R1 R2) R3) x z)
              :by ((q/ex-intro V (lambda [k V]
                                   (and ((rcomp T U V R1 R2) x k)
                                        (R3 k z))) t) <f>)))
      (have <h> _ :by ((q/ex-elim V (lambda [k V]
                                      (and (R2 y k) (R3 k z)))
                                  ((rcomp T V W (rcomp T U V R1 R2) R3) x z))
                       <b> <g>)))
    (have <i> _ :by ((q/ex-elim U (lambda [k U]
                                    (and (R1 x k) ((rcomp U V W R2 R3) k z)))
                                ((rcomp T V W (rcomp T U V R1 R2) R3) x z))
                     <a> <h>))
    (qed <i>)))

(deflemma rcomp-assoc-subrel
  [[T :type] [U :type] [V :type] [W :type]
   [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)]]
  (subrel T W
          (rcomp T U W R1 (rcomp U V W R2 R3))
          (rcomp T V W (rcomp T U V R1 R2) R3)))

(proof rcomp-assoc-subrel
    :script
  (assume [x T
           y W
           H ((rcomp T U W R1 (rcomp U V W R2 R3)) x y)]
    (have <a> ((rcomp T V W (rcomp T U V R1 R2) R3) x y)
          :by ((rcomp-assoc-subrel-aux
                T U V W R1 R2 R3)
               x y H))
    (qed <a>)))

(deflemma rcomp-assoc-suprel-aux
  [[T :type] [U :type] [V :type] [W :type]
   [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)] [x T] [z W]]
  (==> ((rcomp T V W (rcomp T U V R1 R2) R3) x z)
       ((rcomp T U W R1 (rcomp U V W R2 R3)) x z)))

(proof rcomp-assoc-suprel-aux
    :script
  (assume [H ((rcomp T V W (rcomp T U V R1 R2) R3) x z)]
    (have <a> (exists [y V]
                (and ((rcomp T U V R1 R2) x y)
                     (R3 y z))) :by H)
    (assume [y V
             Hy (and ((rcomp T U V R1 R2) x y)
                     (R3 y z))]
      (have <b> (exists [t U] (and (R1 x t) (R2 t y)))
            :by (p/and-elim-left% Hy))
      (assume [t U
               Ht (and (R1 x t) (R2 t y))]
        (have <c1> (R1 x t) :by (p/and-elim-left% Ht))
        (have <c2> (and (R2 t y) (R3 y z))
              :by (p/and-intro% (p/and-elim-right% Ht)
                                (p/and-elim-right% Hy)))
        (have <c3> ((rcomp U V W R2 R3) t z)
              :by ((q/ex-intro V (lambda [k V]
                                   (and (R2 t k) (R3 k z))) y)
                   <c2>))
        (have <c> ((rcomp T U W R1 (rcomp U V W R2 R3)) x z)
              :by ((q/ex-intro U (lambda [k U]
                                   (and (R1 x k)
                                        ((rcomp U V W R2 R3) k z))) t)
                   (p/and-intro% <c1> <c3>))))
      (have <d> _ :by ((q/ex-elim U (lambda [t U] (and (R1 x t) (R2 t y)))
                                  ((rcomp T U W R1 (rcomp U V W R2 R3)) x z))
                       <b> <c>)))
    (have <e> _ :by ((q/ex-elim V (lambda [y V]
                                    (and ((rcomp T U V R1 R2) x y)
                                         (R3 y z)))
                                ((rcomp T U W R1 (rcomp U V W R2 R3)) x z))
                     <a> <d>))
    (qed <e>)))

(deflemma rcomp-assoc-suprel
  [[T :type] [U :type] [V :type] [W :type]
   [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)]]
  (subrel T W
          (rcomp T V W (rcomp T U V R1 R2) R3)
          (rcomp T U W R1 (rcomp U V W R2 R3))))


(proof rcomp-assoc-suprel
    :script
  (assume [x T
           z W]
    (have <a> _ :by (rcomp-assoc-suprel-aux
                     T U V W
                     R1 R2 R3 x z))
    (qed <a>)))

(defthm rcomp-assoc
  "Relational composition is associative."
  [[T :type] [U :type] [V :type] [W :type]
   [R1 (rel T U)] [R2 (rel U V)] [R3 (rel V W)]]
  (releq T W
         (rcomp T U W R1 (rcomp U V W R2 R3))
         (rcomp T V W (rcomp T U V R1 R2) R3)))

(proof rcomp-assoc
    :script
  (have <a> _ :by (p/and-intro% (rcomp-assoc-subrel T U V W R1 R2 R3)
                                (rcomp-assoc-suprel T U V W R1 R2 R3)))
  (qed <a>))

(definition psubrel
  "The anti-reflexive variant of [[subrel]]."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (and (subrel T U R1 R2)
       (not (releq T U R1 R2))))


(defthm psubrel-antirefl
  [[T :type] [U :type] [R (rel T U)]]
  (not (psubrel T U R R)))

(proof psubrel-antirefl
    :script
  (assume [H (psubrel T U R R)]
    (have <a> (not (releq T U R R))
          :by (p/and-elim-right% H))
    (have <b> p/absurd :by (<a> (releq-refl T U R)))
    (qed <b>)))

(defthm psubrel-antisym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (not (and (psubrel T U R1 R2)
            (psubrel T U R2 R1))))

(proof psubrel-antisym
    :script
  (assume [H (and (psubrel T U R1 R2)
                  (psubrel T U R2 R1))]
    (have <a> (not (releq T U R1 R2))
          :by (p/and-elim-right% (p/and-elim-left% H)))
    (have <b> (releq T U R1 R2)
          :by (p/and-intro% (p/and-elim-left% (p/and-elim-left% H))
                            (p/and-elim-left% (p/and-elim-right% H))))
    (have <c> p/absurd :by (<a> <b>))
    (qed <c>)))

(defthm psubrel-trans
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (==> (psubrel T U R1 R2)
       (psubrel T U R2 R3)
       (psubrel T U R1 R3)))

(proof psubrel-trans
    :script
  (assume [H1 (psubrel T U R1 R2)
           H2 (psubrel T U R2 R3)]
    (have <a> (subrel T U R1 R3)
          :by ((subrel-trans T U R1 R2 R3)
               (p/and-elim-left% H1)
               (p/and-elim-left% H2)))
    (assume [H3 (releq T U R1 R3)]
      (have <b> (rel-equal T U R1 R3)
            :by ((releq-implies-rel-equal-ax T U R1 R3)
                 H3))
      (have <c> (psubrel T U R3 R2)
            :by ((rel-equal-prop T U R1 R3 (lambda [R (rel T U)]
                                             (psubrel T U R R2)))
                 <b> H1))
      (have <d> p/absurd :by ((psubrel-antisym T U R2 R3)
                              (p/and-intro% H2 <c>))))
    (have <e> _ :by (p/and-intro% <a> <d>))
    (qed <e>)))

(defthm psubrel-emptyrel
  [[T :type] [U :type] [R (rel T U)]]
  (==> (psubrel T U (emptyrel T U) R)
       (not (releq T U R (emptyrel T U)))))

(proof psubrel-emptyrel
    :script
  (assume [H (psubrel T U (emptyrel T U) R)]
    (assume [H' (releq T U R (emptyrel T U))]
      (have <a> (not (releq T U (emptyrel T U) R))
            :by (p/and-elim-right% H))
      (have <b> (releq T U (emptyrel T U) R)
            :by ((releq-sym T U R (emptyrel T U)) H'))
      (have <c> p/absurd :by (<a> <b>))
      (qed <c>))))


(defthm psubrel-emptyrel-conv
  [[T :type] [U :type] [R (rel T U)]]
  (==> (not (releq T U R (emptyrel T U)))
       (psubrel T U (emptyrel T U) R)))

(proof psubrel-emptyrel-conv
    :script
  (assume [H (not (releq T U R (emptyrel T U)))]
    (have <a> (subrel T U (emptyrel T U) R)
          :by (subrel-emptyrel-lower-bound T U R))
    (assume [H' (releq T U (emptyrel T U) R)]
      (have <b> (releq T U R (emptyrel T U))
            :by ((releq-sym T U (emptyrel T U) R) H'))
      (have <c> p/absurd :by (H <b>)))
    (have <d> (psubrel T U (emptyrel T U) R)
          :by (p/and-intro% <a> <c>))
    (qed <d>)))

(defthm psubrel-emptyrel-equiv
  [[T :type] [U :type] [R (rel T U)]]
  (<=> (psubrel T U (emptyrel T U) R)
       (not (releq T U R (emptyrel T U)))))

(proof psubrel-emptyrel-equiv
    :script
  (have <a> _ :by (p/and-intro% (psubrel-emptyrel T U R)
                                (psubrel-emptyrel-conv T U R)))
  (qed <a>))


