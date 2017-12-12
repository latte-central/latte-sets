(ns latte-sets.pfun
  "Partial functions are defined in this namespace as
  a relation (in the type theoretic sense) of type
  `(==> A B :type)` together with a domain set `sA` and a range set `sB`
   such that for any element of the domain `sA` there is a unique
  image in the range `sB`."
  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof qed lambda]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as s :refer [set elem seteq subset forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel]]))


(definition pfun-ex-def
  "A partial function `f` based on a relation together with
a domain set `dom` and a range set `ran`. This is the existential condition."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]]
  (forall-in [x T dom]
    (exists-in [y U ran]
      (f x y))))

(definition pfun-single-def
  "The singleness condition for partial functions."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]]
  (forall-in [x T dom]
    (forall [y1 y2 U]
      (==> (elem y1 ran)
           (elem y2 ran)
           (f x y1)
           (f x y2)
           (equal y1 y2)))))

(definition pfun-def
  "A partial function `f` based on a relation together with
a domain set `dom` and a range set `ran`."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]]
  (and (pfun-ex-def T U f dom ran)
       (pfun-single-def T U f dom ran)))

(defimplicit pfun
  "A partial function `f` based on a relation together with
a domain set `dom` and a range set `ran`, cf. [[pfun-def]]."
  [def-env ctx [f f-ty] [dom dom-ty] [ran ran-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pfun-def T U f dom ran)))

(defthm pfun-ex-prop
  "The existential property of partial functions, cf [[pfun-ex-def]]."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)] [pf (pfun f dom ran)]]
  (forall-in [x T dom]
    (exists-in [y U ran]
      (f x y))))

(proof 'pfun-ex-prop
  (qed (p/and-elim-left pf)))

(defthm pfun-single-prop
  "The singleness property of partial functions, cf [[pfun-single-def]]."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)] [pf (pfun f dom ran)]]
  (forall-in [x T dom]
    (forall [y1 y2 U]
      (==> (elem y1 ran)
           (elem y2 ran)
           (f x y1)
           (f x y2)
           (equal y1 y2)))))

(proof 'pfun-single-prop
  (qed (p/and-elim-right pf)))

;; the definition of a partial function should in most
;; cases treated as opaque
(latte.utils/set-opacity! #'pfun-def true)

(defn fetch-pfun-type [def-env ctx t]
  (latte.utils/decomposer
   (fn [t]
     (if (clojure.core/and (seq? t)
                           (= (count t) 6)
                           (= (first t) #'latte-sets.pfun/pfun-def))
       (into [] (rest t))
       (throw (ex-info "Not a partial function type." {:type t}))))
   def-env ctx t))

(defimplicit pfun-ex
  "The existential property of partial functions, cf. [[pfun-ex-prop]]."
  [def-env ctx [pf pf-ty]]
  (let [[T U f dom ran] (fetch-pfun-type def-env ctx pf-ty)]
    (list #'pfun-ex-prop T U f dom ran pf)))

(defimplicit pfun-single
  "The singleness property of partial functions, cf. [[pfun-single-prop]]."
  [def-env ctx [pf pf-ty]]
  (let [[T U f dom ran] (fetch-pfun-type def-env ctx pf-ty)]
    (list #'pfun-single-prop T U f dom ran pf)))

(defaxiom pfun-img-ax
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  U)

(defimplicit pfun-img
  "The image of `x` in domain of partial function `f`."
  [def-env ctx [pf pf-ty] [x x-ty] [xin xin-ty]]
  (let [[T U f dom ran] (fetch-pfun-type def-env ctx pf-ty)]
    (list #'pfun-img-ax T U f dom ran pf x xin)))

(defaxiom pfun-img-prop-ax
  "The unique image of an element `x` in the domain of partial function `f`."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  (and (elem (pfun-img pf x xin) ran)
       (f x (pfun-img pf x xin))))

(defimplicit pfun-img-prop
  "The unique image of an element `x` in the domain of partial function `f`."
  [def-env ctx [pf pf-ty] [x x-ty] [xin xin-ty]]
  (let [[T U f dom ran] (fetch-pfun-type def-env ctx pf-ty)]
    (list #'pfun-img-prop-ax T U f dom ran pf x xin)))

(defthm pfun-img-uniq-prop
  "The image of an element `x` by partial function `f` is unique."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  (forall-in [y U ran]
    (==> (f x y)
         (equal y (pfun-img pf x xin)))))

(proof 'pfun-img-uniq-prop
  (pose img := (pfun-img pf x xin))
  (assume [y U
           Hy1 (elem y ran)
           Hy2 (f x y)]
    (have <a> (equal y img)
          :by ((pfun-single pf)
               x xin y img               
               Hy1
               (p/and-elim-left (pfun-img-prop pf x xin))
               Hy2
               (p/and-elim-right (pfun-img-prop pf x xin)))))
  (qed <a>))

(defimplicit pfun-img-uniq
  "`(pfun-img-uniq [f (rel T U)] [dom (set T)] [ran (set U)] [pf (pfun f dom ran)] [x T] [xin (set T)])`

The image of an element `x` by partial function `f` is unique, cf. [[pfun-img-unique-prop]]."
  [def-env ctx [f f-ty] [dom dom-ty] [ran ran-ty] [pf pf-ty] [x x-ty] [xin xin-ty]]
  (let [[T U f dom ran] (fetch-pfun-type def-env ctx pf-ty)]
    (list #'pfun-img-uniq-prop T U f dom ran pf x xin)))

(definition pfinjective-def
  "An injective partial function."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)] [pf (pfun f dom ran)]]
  (forall-in [x1 T dom]
    (forall-in [x2 T dom]
      (forall-in [y1 U ran]
        (forall-in [y2 U ran]
          (==> (f x1 y1)
               (f x2 y2)
               (equal y1 y2)
               (equal x1 x2)))))))


