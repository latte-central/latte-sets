(ns latte-sets.rel
  "A **relation** from elements of
a given type `T` to elements of `U` is formalized with type `(==> T U :type)`.

  This namespace provides some important properties about such
  relations."

  (:refer-clojure :exclude [and or not identity])

  (:require [latte.core :as latte :refer [definition defaxiom defthm
                                          forall lambda ==>
                                          proof assume have]]
            [latte.prop :as p :refer [and or not]]
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
