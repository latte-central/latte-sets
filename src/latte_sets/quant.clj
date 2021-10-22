(ns latte-sets.quant
  "Quantifiers over sets (rather than types), with most
  definitions specialized from [[latte-prelude.quant]]."

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation defimplicit
                                          proof qed assume have pose lambda forall example]]
            [latte.utils :as u]
            [latte-sets.set :as s :refer [set elem]]
            [latte-prelude.prop :as p :refer [and or not]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.equal :as eq :refer [equal]]))

(defnotation forall-in
  "Universal quantification over sets.

  `(forall-in [x s] (P x))` is a 
shortcut for `(forall [x (element-type-of s)]
                 (==> (elem x s)
                      (P x)))`."
  [binding body]
  (if (not= (count binding) 2)
    [:ko {:msg "Binding of `forall-in` should be of the form `[x s]` with `s` a set."
          :binding binding}]
    [:ok (list 'forall [(first binding) (list #'s/element-type-of (second binding))]
               (list '==> (list #'elem (first binding) (second binding))
                     body))]))

(alter-meta! #'forall-in update-in [:style/indent] (fn [_] [1 :form]))

(defn decompose-forall-in-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (let [[[x A] B] (q/decompose-forall-type def-env ctx t)
           [C D] (p/decompose-impl-type def-env ctx B)]
       (let [s (if (seq C)
                 (cond
                   (= (first C) #'s/elem) (nth C 2)
                   (= (first C) #'s/elem-def) (nth C 3)
                   :else
                   (let [m (meta C)]
                     (or (and m (get m :s/elem-set))
                         nil))))]
         [[x A s] D])))
   def-env ctx t))

;; Example without the notation
;; (latte/try-example [[A :type] [As (set A)]]
;;     (forall [x A]
;;       (==> (elem x As)
;;            (elem x As)))
;;   (assume [x A
;;            Hx (elem x As)]
;;     (have <a> (elem x As) :by Hx))
;;   (qed <a>))

;; Example with the notation
;; (latte/try-example [[A :type] [As (set A)]]
;;     (forall-in [x As]
;;       (elem x As))
;;   (assume [x A
;;            Hx (elem x As)]
;;     (have <a> (elem x As) :by Hx))
;;   (qed <a>))

(defnotation exists-in
  "Existential quantification over sets.

  `(exists-in [x s] (P x))` is a 
shortcut for `(exists [x (element-type-of s)]
                 (and (elem x s)
                      (P x)))`."
  [binding body]
  (if (not= (count binding) 2)
    [:ko {:msg "Binding of `exists-in` should be of the form `[x s]`."
          :binding binding}]
    [:ok (list #'exists [(first binding) (list #'s/element-type-of (second binding))]
               (list 'and (list #'elem (first binding) (second binding))
                     body))]))

(alter-meta! #'exists-in update-in [:style/indent] (fn [_] [1 :form]))

;; Example with the notation
;; (latte/try-example [[A :type] [As (set A)] [z A] [Pz (elem z As)]]
;;     (exists [x A]
;;       (and (elem x As)
;;            (elem x As)))
;;   (have <a> (and (elem z As) (elem z As)) :by (p/and-intro Pz Pz))
;;   (qed ((q/ex-intro (lambda [x A] (and (elem x As) (elem x As))) z) <a>)))

;; Example without
;; (latte/try-example [[A :type] [As (set A)] [z A] [Pz (elem z As)]]
;;     (exists-in [x As]
;;       (elem x As))
;;   (have <a> (and (elem z As) (elem z As)) :by (p/and-intro Pz Pz))
;;   (qed ((q/ex-intro (lambda [x A] (and (elem x As) (elem x As))) z) <a>)))


(defn decompose-exists-in-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (let [[A B] (q/decompose-ex-type def-env ctx t)]
       (let [[[y _] C] (p/decompose-lambda-term def-env ctx B)
             [D E] (p/decompose-and-type def-env ctx C)]
         (if (seq D)
           (cond
             (= (first D) #'s/elem) [[y A (nth D 2)] E]
             (= (first D) #'s/elem-def) [[y A (nth D 3)] E]
             :else
             (let [m (meta D)
                   s (or (and m (get m :s/elem-set))
                         nil)]
               [[y A s] E]))
           (throw (ex-info "Cannot decompose exists-in type" {:type t}))))))
   def-env ctx t))

(defthm ex-in-elim-rule
  "Elimination rule for `exists-in` existentials, a set-theoretic variant of [[latte-prelude.quant/ex-elim-rule]]."
  [[?T :type] [s (set T)] [P (==> T :type)] [A :type]]
  (==> (exists-in [x s] (P x))
       (forall-in [y s]
         (==> (P y) A))
       A))

(proof 'ex-in-elim-rule-thm
  (assume [Hex _
           HA _]
    (pose Q := (lambda [x T] (and (elem x s) (P x))))
    (assume [z T
             Hz (Q z)]
      (have <a> A :by (HA z (p/and-elim-left Hz) (p/and-elim-right Hz))))
    (have <b> A :by (q/ex-elim Hex <a>)))
  (qed <b>))

(defimplicit ex-in-elim
  "The elimination rule for the `exists-in` existential quantifier over a set `s` (of elements of type `T`).
A typical proof instance is of the form `(ex-in-elim ex-proof A-proof)`
with `ex-term` a proof of `(exists-in [x s] (P x))` and `A-proof` a proof of  `(==> (forall-in [x s] (==> (P x) A)))`. See [[ex-in-elem-rule]]."
  [def-env ctx [ex-proof ex-ty] [A-proof A-proof-ty]]
  (let [[[y T s] Py] (decompose-exists-in-type def-env ctx ex-ty)
        [_ PA] (decompose-forall-in-type def-env ctx A-proof-ty)
        [_ A] (p/decompose-impl-type def-env ctx PA)]
    [[(list #'ex-in-elim-rule-thm T s (list 'λ [y T] Py) A) ex-proof] A-proof]))

(example [[T :type] [s (set T)] [A :type] [P (==> T :type)] [Hex (exists-in [y s] (P y))]]
    (==> (forall-in [x s] (==> (P x) A))
         A)
  ;; proof
  (assume [Hx (forall-in [x s] (==> (P x) A))]
    (have <a> A :by (ex-in-elim Hex Hx)))
  (qed <a>))
  
(defthm ex-in-intro
  "The introduction rule for the `exists-in` quantifier, cf. [[latte-prelude.quant/ex-intro-thm]]."
  [[?T :type] [s (set T)] [P (==> T :type)] [x T]]
  (==> (elem x s)
       (P x)
       (exists-in [y s] (P y))))

(proof 'ex-in-intro-thm
  (assume [H1 _ H2 _]
    (pose Q := (lambda [y T] (and (elem y s) (P y))))
    (have <a> (exists [y T]
                (and (elem y s)
                     (P y))) :by ((q/ex-intro Q x) (p/and-intro H1 H2))))
  (qed <a>))

(definition single-in
  "The constraints that \"there exists at most one element of type `T`
in set `s` such that...\"

This is a set-theoretic variant of [[latte-prelude.quant/single]]."
  [[?T :type] [s (set T)] [P (==> T :type)]]
  (forall-in [x s]
    (forall-in [y s]
      (==> (P x)
           (P y)
           (equal x y)))))

(defn decompose-single-in-type [def-env ctx t]
  (u/decomposer
   (fn [t]
     (if (clojure.core/and (seq t)
                           (= (count t) 4)
                           (= (first t) #'latte-sets.quant/single-in-def))
       [(second t) (nth t 2) (nth t 3)]
       (throw (ex-info "Cannot infer a \"single-in\" type" {:type t}))))
   def-env ctx t))

(defthm single-in-intro
  "Introduction rule for [[single-in]]."
  [?T :type, s (set T), P (==> T :type)]
  (==> (forall-in [x s]
         (forall-in [y s]
           (==> (P x)
                (P y)
                (equal x y))))
       (single-in s P)))

(proof 'single-in-intro-thm
  (assume [H _]
    (have <a> (single-in s P) :by H))
  (qed <a>))

(defthm single-in-elim-rule
  "Elimination rule for [[single-in]]."
  [?T :type, s (set T), P (==> T :type), x T, y T]
  (==> (single-in s P)
       (elem x s)
       (elem y s)
       (P x)
       (P y)
       (equal x y)))

(proof 'single-in-elim-rule-thm
  (assume [Hsingle _
           Hx _ Hy _
           HPx _ HPy _]
    (have <a> (equal x y) :by (Hsingle x Hx y Hy HPx HPy)))
  (qed <a>))

(defimplicit single-in-elim
  "Elimination rule for [[single-in]]. `(single-in-elim s-proof x y)`
 such that the type of `s-proof` is `(single-in s P)` for some property `P`, then
 we have `(==> (P x) (P y) (equal x y))` thanks to `[[single-in-elim-rule]]`."
  [def-env ctx [s-proof s-proof-type] [x x-type] [y y-type]]
  (let [[T s P] (decompose-single-in-type def-env ctx s-proof-type)]
    [(list #'single-in-elim-rule-thm T s P x y) s-proof]))

(example [[T :type] [s (set T)] [P (==> T :type)] [Hs (single-in s P)] [x T] [y T]]
    (==> (elem x s)
         (elem y s)
         (P x)
         (P y)
         (equal x y))
  ;; proof
  (assume [Hx (elem x s)
           Hy (elem y s)
           HPx (P x)
           HPy (P y)]
    (have <a> (equal x y) :by ((single-in-elim Hs x y) Hx Hy HPx HPy)))
  (qed <a>))

;; single-in is made opaque
(u/set-opacity! #'single-in-def true)

(definition unique-in
  "The constraint that \"there exists a unique element of type `T`
 in set `s` such that ...\".

This is a set-theoretic variant of [[latte-prelude.quant/unique-prop]]."
  [[?T :type] [s (set T)] [P (==> T :type)]]
  (and (exists-in [x s] (P x))
       (single-in s P)))

(defaxiom the-element-ax
  "The unique element descriptor axiom.

This is a set-theoretic variant of [[latte-prelude.quant/the-ax]]."
  [[T :type] [s (set T)] [P (==> T :type)] [u (unique-in s P)]]
  T)

(defimplicit the-element
  "The unique element descriptor for sets.

`(the-element u)` defines the unique element of
 set `s` satisfying the predicate `P`. This is provided
 thanks to the uniqueness proof `u` (of type `(unique-in s P)`.

This is the set-theoretic version of the [[latte-prelude.quant/the]]."
  [def-env ctx [u u-ty]]
  (let [[_ S] (p/decompose-and-type def-env ctx u-ty)
        [T s P] (decompose-single-in-type def-env ctx S)]
    (list #'the-element-ax T s P u)))

(example [[T :type] [s (set T)] [P (==> T :type)]]
    (==> (exists-in [x s] (P x))
         (single-in s P)
         T)
  ;; proof
  (assume [Hex _
           Hs _]
    (have <a> T :by (the-element (p/and-intro Hex Hs))))
  (qed <a>))

(defaxiom the-element-prop-ax
  "The property of the unique element descriptor, cf. [[latte-prelude.quant/the-prop-ax]]."
  [[T :type] [s (set T)] [P (==> T :type)] [u (unique-in s P)]]
  (and (elem (the-element u) s)
       (P (the-element u))))

(defimplicit the-element-prop
   "`(the-element-prop u)` proves `(P (the-element u))` from the proof `u` of `(unique-in s P)`, for some property `P` and set `s`. This is the main property of the unique descriptor [[the-element]], cf [[the-element-prop-ax]]."
  [def-env ctx [u u-ty]]
  (let [[_ S] (p/decompose-and-type def-env ctx u-ty)
        [T s P] (decompose-single-in-type def-env ctx S)]
    (list #'the-element-prop-ax T s P u)))

(example [[T :type] [s (set T)] [P (==> T :type)] [u (unique-in s P)]]
    (P (the-element u))
  ;; proof
  (qed (p/and-elim-right (the-element-prop u))))

(defthm the-element-lemma-prop
  "The unique element ... in `s` is ... unique, cf [[latte-prelude.quand/the-lemma-thm]]."
  [[?T :type] [s (set T)] [P (==> T :type)] [u (unique-in s P)]]
  (forall-in [y s]
    (==> (P y)
         (equal y (the-element u)))))

(proof 'the-element-lemma-prop-thm
  (have <a> (single-in s P) :by (p/and-elim-right u))
  (have <b> (elem (the-element u) s) :by (p/and-elim-left (the-element-prop u)))
  (have <c> (P (the-element u)) :by (p/and-elim-right (the-element-prop u)))
  (assume [y T Hy (elem y s)
           HPy (P y)]
    (have <d> (equal y (the-element u)) 
          :by ((single-in-elim <a> y (the-element u)) Hy <b> HPy <c>)))
  (qed <d>))

(defimplicit the-element-lemma
  "`(the-element-lemma u)` proves that `(forall-in [y s] (==> (P y) (equal y (the-element u))))`
from the proof `u` that `(unique-in s P)` for some property `P` and set `s`."
  [def-env ctx [u u-ty]]
  (let [[_ S] (p/decompose-and-type def-env ctx u-ty)
        [T s P] (decompose-single-in-type def-env ctx S)]
    (list #'the-element-lemma-prop-thm T s P u)))



    
