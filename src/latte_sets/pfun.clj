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
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-sets.core :as s :refer [set elem seteq subset forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel dom ran]]))


(definition pfun-def
  "A partial function `f` based on a relation together with
a domain set `from` and a range set `to`. Note that the relation `f` on
outside `from` or `to` need not be a function."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x from]
    (forall-in [y1 to]
      (forall-in [y2 to]
        (==> (f x y1)
             (f x y2)
             (equal y1 y2))))))

(defimplicit pfun
  "The term `(pfun f from to)` means the relation `f` is a partial function over the
domain set `from` and range set `to`, cf. [[pfun-def]]."
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

(definition ptotal-def
  "The partial function `f` is total wrt. the provided `from`/`to` sets."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x from]
    (exists-in [y to]
      (f x y))))

(defimplicit ptotal
  "The term `(ptotal f from to)` means the partial function `f` is
total wrt. the provided `from`/`to` sets, cf. [[ptotal-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'ptotal-def T U f from to)))


(definition application
  "An application is a total function on its whole domain/range."
  [[T :type] [U :type] [f (rel T U)]]
  (and (pfun f (dom f) (ran f))
       (ptotal f (dom f) (ran f))))

(definition pinjective-def
  "An injective partial function."
  [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x1 from]
    (forall-in [x2 from]
      (forall-in [y1 to]
        (forall-in [y2 to]
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
  (forall-in [y to]
    (exists-in [x from]
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

(comment
  (defthm pinjective-single
    [[T :type] [U :type] [f (rel T U)] [from (set T)] [to (set U)]]
    (==> (pfun f from to)
         (pinjective f from to)
         (forall-in [z to]
                    (q/single (lambda [x T] (and (elem x from) 
                                                 (forall [w U] 
                                                         (==> (f x w)
                                                              (equal w z)))))))))

(proof 'pinjective-single
  (assume [Hfun _
           Hinj _
           z U
           Hz (elem z to)]
    (pose P := (lambda [x T] (and (elem x from)
                                  (forall [w U]
                                    (==> (f x w)
                                         (equal w z))))))
    (assume [x T y T
             Hx (P x)
             Hy (P y)]
      "We have to show that x equals y"
      (have <a1> (elem x from) :by (p/and-elim-left Hx))
      (have <a2> (elem y from) :by (p/and-elim-left Hy))
      )))


)
      
