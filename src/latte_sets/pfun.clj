(ns latte-sets.pfun
  "Partial functions are defined in this namespace as
  a relation (in the type theoretic sense) of type
  `(==> T U :type)` together with a domain `dom` of type `(set T)`
  and a range `ran` of type `(set U)`
   such that for any element of the domain there is a unique
  image in the range.

  **Remark**: in type theory, it is best to rely on total functions because
  these are 'native' through the function type `==>`. Partial functions are encoded and thus more complex and less 'natural', use with care."

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof qed lambda]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as s :refer [set elem seteq subset forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel]]))


(definition pfun-def
  "A partial function `f` based on a relation together with
a domain set `from` and a range set `to`."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x T from]
    (forall-in [y1 U to]
      (forall-in [y2 U to]
        (==> (f x y1)
             (f x y2)
             (equal y1 y2))))))

(defimplicit pfun
  "A partial function `f` based on a relation together with
a domain set `from` and a range set `to`, cf. [[pfun-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pfun-def T U f from to)))

(defn fetch-pfun-type [def-env ctx t]
  (latte.utils/decomposer
   (fn [t]
     (if (clojure.core/and (seq? t)
                           (= (count t) 6)
                           (= (first t) #'latte-sets.pfun/pfun-def))
       (into [] (rest t))
       (throw (ex-info "Not a partial function type." {:type t}))))
   def-env ctx t))

(definition pinjective-def
  "An injective partial function."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x1 T from]
    (forall-in [x2 T from]
      (forall-in [y1 U to]
        (forall-in [y2 U to]
          (==> (f x1 y1)
               (f x2 y2)
               (equal y1 y2)
               (equal x1 x2)))))))

(defimplicit pinjective
  "An injective partial function, cf. [[pinjective-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pinjective-def T U f from to)))

(definition psurjective-def
  "A surjective partial function."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [y U to]
    (exists-in [x T from]
      (f x y))))

(defimplicit psurjective
  "An surjective partial function, cf. [[psurjective-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'psurjective-def T U f from to)))

(definition pbijective-def
  "A bijective partial function."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (and (pinjective f from to)
       (psurjective f from to)))

(defimplicit pbijective
  "An bijective partial function, cf. [[pbijective-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'pbijective-def T U f from to)))


