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


(definition pfun-ex
  "A partial function `f` based on a relation together with
a domain set `dom` and a range set `ran`. This is the existential condition."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]]
  (forall-in [x T dom]
    (exists-in [y U ran]
      (f x y))))

(definition pfun-single
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
  (and (pfun-ex T U f dom ran)
       (pfun-single T U f dom ran)))

(defimplicit pfun
  "A partial function `f` based on a relation together with
a domain set `dom` and a range set `ran`, cf. [[pfun-def]]."
  [def-env ctx [f f-ty] [dom dom-ty] [ran ran-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pfun-def T U f dom ran)))

(defaxiom pfun-img-ax
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  U)

(defimplicit pfun-img
  "The image of `x` in domain of partial function `f`."
  [def-env ctx [f f-ty] [dom dom-ty] [ran ran-ty] [pf pf-ty] [x x-ty] [xin xin-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pfun-img-ax T U f dom ran pf x xin)))

(defaxiom pfun-img-prop-ax
  "The unique image of an element `x` in the domain of partial function `f`."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  (and (elem (pfun-img f dom ran pf x xin) ran)
       (f x (pfun-img f dom ran pf x xin))))

(defimplicit pfun-img-prop
  "The unique image of an element `x` in the domain of partial function `f`."
  [def-env ctx [f f-ty] [dom dom-ty] [ran ran-ty] [pf pf-ty] [x x-ty] [xin xin-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pfun-img-prop-ax T U f dom ran pf x xin)))

(defthm pfun-img-uniq-prop
  "The image of an element `x` by partial function `f` is unique."
  [[T :type] [U :type] [f (rel T U)] [dom (set T)] [ran (set U)]
   [pf (pfun f dom ran)] [x T] [xin (elem x dom)]]
  (forall-in [y U ran]
    (==> (f x y)
         (equal y (pfun-img f dom ran pf x xin)))))

(proof 'pfun-img-uniq-prop
  (pose img := (pfun-img f dom ran pf x xin))
  (assume [y U
           Hy1 (elem y ran)
           Hy2 (f x y)]
    (have <a> (equal y img)
          :by ((p/and-elim-right pf)
               x xin y img               
               Hy1
               (p/and-elim-left (pfun-img-prop f dom ran pf x xin))
               Hy2
               (p/and-elim-right (pfun-img-prop f dom ran pf x xin)))))
  (qed <a>))


