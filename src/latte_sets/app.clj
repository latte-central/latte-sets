(ns latte-sets.app
  "An application ... (TODO)"

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof qed lambda]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-sets.set :as s :refer [set elem seteq subset forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel dom ran]]))

(definition app-def
  "The relation `f` is an application."
  [[T :type] [U :type] [f (rel T U)]]
  (forall-in [x (dom f)]
    (forall-in [y1 (ran f)]
      (forall-in [y2 (ran f)]
        (==> (f x y1)
             (f x y2)
             (equal y1 y2))))))

(defimplicit app
  "The term `(app f)` means the relation `f` is an application, cf. [[app-def]]."
  [def-env ctx [f f-ty] [from from-ty] [to to-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'app-def T U f from to)))

(defn fetch-app-type [def-env ctx t]
  (latte.utils/decomposer
   (fn [t]
     (if (clojure.core/and (seq? t)
                           (= (count t) 3)
                           (= (first t) #'latte-sets.app/app-def))
       (into [] (rest t))
       (throw (ex-info "Not an application." {:type t}))))
   def-env ctx t))

(definition injective-def
  "An application is injective."
  [[T :type] [U :type] [f (rel T U)]]
  (forall-in [x1 (dom f)]
    (forall-in [x2 (dom f)]
      (forall-in [y1 (ran f)]
        (forall-in [y2 (ran f)]
          (==> (f x1 y1)
               (f x2 y2)
               (equal y1 y2)
               (equal x1 x2)))))))

(defimplicit injective
  "The application `f` is injective, cf. [[injective-def]]."
  [def-env ctx [f f-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'injective-def T U f)))

(definition surjective-def
  "An application is surjective."
  [[T :type] [U :type] [f (rel T U)]]
  (forall-in [y (ran f)]
    (exists-in [x (dom f)]
      (f x y))))

(defimplicit surjective
  "The application `f` is surjective, cf. [[surjective-def]]."
  [def-env ctx [f f-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'surjective-def T U f)))

(definition bijective-def
  "The application `f` is bijective."
  [[T :type] [U :type] [f (rel T U)]]
  (and (injective f)
       (surjective f)))

(defimplicit pbijective
  "The term `(bijective f)` means the application `f` is bijective, cf. [[bijective-def]]."
  [def-env ctx [f f-ty]]
  (let [[T U] (rel/fetch-rel-type def-env ctx f-ty)]
    (list #'bijective-def T U f)))




