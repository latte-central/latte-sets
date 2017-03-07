(ns latte-sets.ralgebra
  "The relation algebra operators."

  (:refer-clojure :exclude [and or not set complement])

  (:require [latte.core :as latte
             :refer [definition defthm defaxiom defnotation
                     forall lambda ==>
                     assume have pose proof lambda forall]]
 
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as sets
             :refer [set elem subset seteq set-equal emptyset fullset]]

            [latte-sets.algebra :as alg]

            [latte-sets.rel :as rel
             :refer [rel dom ran subrel releq rel-equal emptyrel fullrel]]))

(definition runion
  "Relational union."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (or (R1 x y)
          (R2 x y)))))

(defthm runion-idem
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U (runion T U R R) R))

(proof runion-idem
    :script
  "We first prove that `R`∪`R`⊆`R`."
  (assume [x T
           y U
           Hxy ((runion T U R R) x y)]
    (have <a> (or (R x y)
                  (R x y)) :by Hxy)
    (assume [Hor (R x y)]
      (have <b> (R x y) :by Hor))
    (have <c> (R x y)
          :by (p/or-elim% <a> (R x y) <b> <b>)))
  "We next prove that `R`⊆ `R`∪`R`"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <d> (or (R x y)
                  (R x y))
          :by (p/or-intro-left% Hxy (R x y))))
  (have <e> _ :by (p/and-intro% <c> <d>))
  (qed <e>))

(defthm runion-empty
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U
         (runion T U R (emptyrel T U))
         R))

(proof runion-empty
    :script
  "subset case"
  (assume [x T
           y U
           Hxy ((runion T U R (emptyrel T U)) x y)]
    (have <a> (or (R x y)
                  ((emptyrel T U) x y)) :by Hxy)
    (assume [H1 (R x y)]
      (have <b> (R x y) :by H1))
    (assume [H2 ((emptyrel T U) x y)]
      (have <c> p/absurd :by H2)
      (have <d> (R x y) :by (<c> (R x y))))
    (have <e> _ :by (p/or-elim% <a> (R x y) <b> <d>)))
  "superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <f> (or (R x y)
                  ((emptyrel T U) x y))
          :by (p/or-intro-left% Hxy ((emptyrel T U) x y))))
  (have <g> _ :by (p/and-intro% <e> <f>))
  (qed <g>))

(defthm runion-commute
  "Set union commutes."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (releq T U
         (runion T U R1 R2)
         (runion T U R2 R1)))

(proof runion-commute :script
  (assume [x T
           y U
           H ((runion T U R1 R2) x y)]
    (have <a1> (or (R1 x y)
                   (R2 x y)) :by H)
    (have <a> _ :by (p/or-sym% <a1>)))
  (assume [x T
           y U
           H ((runion T U R2 R1) x y)]
    (have <b1> (or (R2 x y)
                   (R1 x y)) :by H)
    (have <b> _
          :by (p/or-sym% <b1>)))
  (have <c> _
        :by (p/and-intro% <a> <b>))
  (qed <c>))

(defthm runion-assoc
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (runion T U R1 (runion T U R2 R3))
         (runion T U (runion T U R1 R2) R3)))

(proof runion-assoc
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((runion T U R1 (runion T U R2 R3)) x y)]
    (have <a> (or (R1 x y)
                  ((runion T U R2 R3) x y)) :by Hxy)
    (assume [H1 (R1 x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-left% H1 (R2 x y)))
      (have <b> (or (or (R1 x y)
                        (R2 x y))
                    (R3 x y))
            :by (p/or-intro-left% <b1> (R3 x y))))
    (assume [H2 ((runion T U R2 R3) x y)]
      (have <c1> (or (R2 x y)
                     (R3 x y)) :by H2)
      (assume [H3 (R2 x y)]
        (have <d1> (or (R1 x y)
                       (R2 x y))
              :by (p/or-intro-right% (R1 x y) H3))
        (have <d> (or (or (R1 x y)
                          (R2 x y))
                      (R3 x y))
              :by (p/or-intro-left% <d1> (R3 x y))))
      (assume [H3 (R3 x y)]
        (have <e> (or (or (R1 x y)
                          (R2 x y))
                      (R3 x y))
              :by (p/or-intro-right% (or (R1 x y)
                                         (R2 x y))
                                     H3)))
      (have <c> _ :by (p/or-elim% <c1> (or (or (R1 x y)
                                               (R2 x y))
                                           (R3 x y))
                                  <d> <e>)))
    (have <f> ((runion T U (runion T U R1 R2) R3) x y)
          :by (p/or-elim% <a> (or (or (R1 x y)
                                               (R2 x y))
                                           (R3 x y))
                          <b> <c>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((runion T U (runion T U R1 R2) R3) x y)]
    (have <g> (or ((runion T U R1 R2) x y)
                  (R3 x y)) :by Hxy)
    (assume [H1 ((runion T U R1 R2) x y)]
      (have <h1> (or (R1 x y)
                     (R2 x y)) :by H1)
      (assume [H2 (R1 x y)]
        (have <i> (or (R1 x y)
                      (or (R2 x y)
                          (R3 x y)))
              :by (p/or-intro-left% H2 (or (R2 x y)
                          (R3 x y)))))
      (assume [H3 (R2 x y)]
        (have <j1> (or (R2 x y)
                       (R3 x y))
              :by (p/or-intro-left% H3 (R3 x y)))
        (have <j> (or (R1 x y)
                      (or (R2 x y)
                          (R3 x y)))
              :by (p/or-intro-right% (R1 x y) <j1>)))
      (have <h> _ :by (p/or-elim% <h1> (or (R1 x y)
                                           (or (R2 x y)
                                               (R3 x y)))
                                  <i> <j>)))
    (assume [H2 (R3 x y)]
      (have <j1> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-right% (R2 x y) H2))
      (have <j> (or (R1 x y)
                    (or (R2 x y)
                        (R3 x y)))
            :by (p/or-intro-right% (R1 x y) <j1>)))
    (have <k> ((runion T U R1 (runion T U R2 R3)) x y)
          :by (p/or-elim% <g> (or (R1 x y)
                                  (or (R2 x y)
                                      (R3 x y)))
                          <h> <j>)))
  (have <l> _ :by (p/and-intro% <f> <k>))
  (qed <l>))

(defthm runion-assoc-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (runion T U (runion T U R1 R2) R3)
         (runion T U R1 (runion T U R2 R3))))

(proof runion-assoc-sym
    :script
  (have <a> (releq T U
                   (runion T U R1 (runion T U R2 R3))
                   (runion T U (runion T U R1 R2) R3))
        :by (runion-assoc T U R1 R2 R3))
  (have <b> _ :by ((rel/releq-sym T U
                                   (runion T U R1 (runion T U R2 R3))
                                   (runion T U (runion T U R1 R2) R3))
                   <a>))
  (qed <b>))

(defthm runion-dom
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (seteq T
         (dom T U (runion T U R1 R2))
         (alg/union T
                    (dom T U R1)
                    (dom T U R2))))

(proof runion-dom
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (dom T U (runion T U R1 R2)))]
    (have <a> (exists [y U] ((runion T U R1 R2) x y))
          :by Hx)
    (assume [y U
             Hy ((runion T U R1 R2) x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y)) :by Hy)
      (assume [HR1 (R1 x y)]
        (have <c1> (exists [y U] (R1 x y))
              :by ((q/ex-intro U (lambda [k U] (R1 x k)) y)
                   HR1))
        (have <c2> (elem T x (dom T U R1)) :by <c1>)
        (have <c3> (or (elem T x (dom T U R1))
                       (elem T x (dom T U R2)))
              :by (p/or-intro-left% <c2> (elem T x (dom T U R2))))
        (have <c> (elem T x (alg/union T
                                       (dom T U R1)
                                       (dom T U R2))) :by <c3>))
      (assume [HR2 (R2 x y)]
        (have <d1> (exists [y U] (R2 x y))
              :by ((q/ex-intro U (lambda [k U] (R2 x k)) y)
                   HR2))
        (have <d2> (elem T x (dom T U R2)) :by <d1>)
        (have <d3> (or (elem T x (dom T U R1))
                       (elem T x (dom T U R2)))
              :by (p/or-intro-right% (elem T x (dom T U R1)) <d2>))
        (have <d> (elem T x (alg/union T
                                       (dom T U R1)
                                       (dom T U R2))) :by <d3>))
      (have <e> _ :by (p/or-elim% <b1> 
                                  (elem T x (alg/union T
                                                       (dom T U R1)
                                                       (dom T U R2)))
                                  <c> <d>)))
    (have <f> _ :by ((q/ex-elim U (lambda [k U]
                                    ((runion T U R1 R2) x k))
                                (elem T x (alg/union T
                                                     (dom T U R1)
                                                     (dom T U R2))))
                     <a> <e>)))
  "Supset case"
  (assume [x T
           Hx (elem T x (alg/union T
                                   (dom T U R1)
                                   (dom T U R2)))]
    (have <g> (or (elem T x (dom T U R1))
                  (elem T x (dom T U R2))) :by Hx)
    (assume [HR1 (elem T x (dom T U R1))]
      (have <h> (exists [y U] (R1 x y)) :by HR1)
      (assume [y U
               Hy (R1 x y)]
        (have <i1> (or (R1 x y) (R2 x y))
              :by (p/or-intro-left% Hy (R2 x y)))
        (have <i2> ((runion T U R1 R2) x y) :by <i1>)
        (have <i> (elem T x (dom T U (runion T U R1 R2)))
              :by ((q/ex-intro U (lambda [k U]
                                   ((runion T U R1 R2) x k))
                               y)
                   <i2>)))
      (have <j> _ :by ((q/ex-elim U (lambda [k U] (R1 x k))
                                  (elem T x (dom T U (runion T U R1 R2))))
                       <h> <i>)))
    (assume [HR2 (elem T x (dom T U R2))]
      (have <k> (exists [y U] (R2 x y)) :by HR2)
      (assume [y U
               Hy (R2 x y)]
        (have <l1> (or (R1 x y) (R2 x y))
              :by (p/or-intro-right% (R1 x y) Hy))
        (have <l2> ((runion T U R1 R2) x y) :by <l1>)
        (have <l> (elem T x (dom T U (runion T U R1 R2)))
              :by ((q/ex-intro U (lambda [k U]
                                   ((runion T U R1 R2) x k))
                               y)
                   <l2>)))
      (have <m> _ :by ((q/ex-elim U (lambda [k U] (R2 x k))
                                  (elem T x (dom T U (runion T U R1 R2))))
                       <k> <l>)))
    (have <n> _ :by (p/or-elim% <g> (elem T x (dom T U (runion T U R1 R2)))
                                <j> <m>)))
  (have <o> _ :by (p/and-intro% <f> <n>))
  (qed <o>))


(defthm runion-ran
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (seteq U
         (ran T U (runion T U R1 R2))
         (alg/union U
                    (ran T U R1)
                    (ran T U R2))))

(proof runion-ran
    :script
  "Subset case"
  (assume [y U
           Hy (elem U y (ran T U (runion T U R1 R2)))]
    (have <a> (exists [x T] ((runion T U R1 R2) x y))
          :by Hy)
    (assume [x T
             Hx ((runion T U R1 R2) x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y)) :by Hx)
      (assume [HR1 (R1 x y)]
        (have <c1> (exists [x T] (R1 x y))
              :by ((q/ex-intro T (lambda [k T] (R1 k y)) x)
                   HR1))
        (have <c2> (elem U y (ran T U R1)) :by <c1>)
        (have <c3> (or (elem U y (ran T U R1))
                       (elem U y (ran T U R2)))
              :by (p/or-intro-left% <c2> (elem U y (ran T U R2))))
        (have <c> (elem U y (alg/union U
                                       (ran T U R1)
                                       (ran T U R2))) :by <c3>))
      (assume [HR2 (R2 x y)]
        (have <d1> (exists [x T] (R2 x y))
              :by ((q/ex-intro T (lambda [k T] (R2 k y)) x)
                   HR2))
        (have <d2> (elem U y (ran T U R2)) :by <d1>)
        (have <d3> (or (elem U y (ran T U R1))
                       (elem U y (ran T U R2)))
              :by (p/or-intro-right% (elem U y (ran T U R1)) <d2>))
        (have <d> (elem U y (alg/union U
                                       (ran T U R1)
                                       (ran T U R2))) :by <d3>))
      (have <e> _ :by (p/or-elim% <b1> 
                                  (elem U y (alg/union U
                                                       (ran T U R1)
                                                       (ran T U R2)))
                                  <c> <d>)))
    (have <f> _ :by ((q/ex-elim T (lambda [k T]
                                    ((runion T U R1 R2) k y))
                                (elem U y (alg/union U
                                                     (ran T U R1)
                                                     (ran T U R2))))
                     <a> <e>)))

  "Supset case"
   (assume [y U
            Hy (elem U y (alg/union U
                                    (ran T U R1)
                                    (ran T U R2)))]
     (have <g> (or (elem U y (ran T U R1))
                   (elem U y (ran T U R2))) :by Hy)
     (assume [HR1 (elem U y (ran T U R1))]
       (have <h> (exists [x T] (R1 x y)) :by HR1)
       (assume [x T
                Hx (R1 x y)]
         (have <i1> (or (R1 x y) (R2 x y))
               :by (p/or-intro-left% Hx (R2 x y)))
         (have <i2> ((runion T U R1 R2) x y) :by <i1>)
         (have <i> (elem U y (ran T U (runion T U R1 R2)))
               :by ((q/ex-intro T (lambda [k T]
                                    ((runion T U R1 R2) k y))
                                x)
                    <i2>)))
       (have <j> _ :by ((q/ex-elim T (lambda [k T] (R1 k y))
                                   (elem U y (ran T U (runion T U R1 R2))))
                        <h> <i>)))
     (assume [HR2 (elem U y (ran T U R2))]
       (have <k> (exists [x T] (R2 x y)) :by HR2)
       (assume [x T
                Hx (R2 x y)]
         (have <l1> (or (R1 x y) (R2 x y))
               :by (p/or-intro-right% (R1 x y) Hx))
         (have <l2> ((runion T U R1 R2) x y) :by <l1>)
         (have <l> (elem U y (ran T U (runion T U R1 R2)))
               :by ((q/ex-intro T (lambda [k T]
                                    ((runion T U R1 R2) k y))
                                x)
                    <l2>)))
       (have <m> _ :by ((q/ex-elim T (lambda [k T] (R2 k y))
                                   (elem U y (ran T U (runion T U R1 R2))))
                        <k> <l>)))
     (have <n> _ :by (p/or-elim% <g> (elem U y (ran T U (runion T U R1 R2)))
                                 <j> <m>)))
   (have <o> _ :by (p/and-intro% <f> <n>))
   (qed <o>))


(definition rinter
  "Relational intersection."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (and (R1 x y)
           (R2 x y)))))

(defthm rinter-elim-left
  "Elimination rule for intersection (left operand)."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [x T] [y U]]
  (==> ((rinter T U R1 R2) x y)
       (R1 x y)))

(proof rinter-elim-left
    :script
  (assume [H ((rinter T U R1 R2) x y)]
    (have <a> (R1 x y) :by (p/and-elim-left% H))
    (qed <a>)))

(defthm rinter-elim-right
  "Elimination rule for intersection (right operand)."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [x T] [y U]]
  (==> ((rinter T U R1 R2) x y)
       (R2 x y)))

(proof rinter-elim-right
    :script
  (assume [H ((rinter T U R1 R2) x y)]
    (have <a> (R2 x y) :by (p/and-elim-right% H))
    (qed <a>)))


(defthm rinter-idem
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U
         (rinter T U R R)
         R))

(proof rinter-idem
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter T U R R) x y)]
    (have <a> (and (R x y)
                   (R x y)) :by Hxy)
    (have <b> (R x y) :by (p/and-elim-left% <a>)))
  "Superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <c> (and (R x y)
                   (R x y))
          :by (p/and-intro% Hxy Hxy)))
  (have <d> _ :by (p/and-intro% <b> <c>))
  (qed <d>))

(defthm rinter-empty
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U
         (rinter T U R (emptyrel T U))
         (emptyrel T U)))

(proof rinter-empty
    :script
  "Subset case."
  (assume [x T
           y U
           Hxy ((rinter T U R (emptyrel T U)) x y)]
    (have <a> ((emptyrel T U) x y)
          :by (p/and-elim-right% Hxy)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <b> p/absurd :by Hxy)
    (have <c> _ :by (<b> ((rinter T U R (emptyrel T U)) x y))))
  (have <d> _ :by (p/and-intro% <a> <c>))
  (qed <d>))

(defthm rinter-commute
  "Relation intersection commutes."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (releq T U
         (rinter T U R1 R2)
         (rinter T U R2 R1)))

(proof rinter-commute :script
  (assume [x T
           y U
           Hxy ((rinter T U R1 R2) x y)]
    (have <a> ((rinter T U R2 R1) x y)
          :by ((p/and-sym (R1 x y) (R2 x y)) Hxy)))
  (assume [x T
           y U
           Hxy ((rinter T U R2 R1) x y)]
    (have <b> ((rinter T U R1 R2) x y)
          :by ((p/and-sym (R2 x y) (R1 x y)) Hxy)))
  (have <c> _
        :by (p/and-intro% <a> <b>))
  (qed <c>))

(defthm rinter-assoc
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (rinter T U R1 (rinter T U R2 R3))
         (rinter T U (rinter T U R1 R2) R3)))

(proof rinter-assoc
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter T U R1 (rinter T U R2 R3)) x y)]
    (have <a1> (and (R1 x y)
                    (and (R2 x y)
                         (R3 x y))) :by Hxy)
    (have <a2> (R1 x y) :by (p/and-elim-left% <a1>))
    (have <a3> (R2 x y) :by (p/and-elim-left% (p/and-elim-right% <a1>)))
    (have <a4> (R3 x y) :by (p/and-elim-right% (p/and-elim-right% <a1>)))
    (have <a> _ :by (p/and-intro% (p/and-intro% <a2> <a3>) <a4>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((rinter T U (rinter T U R1 R2) R3) x y)]
    (have <b1> (and (and (R1 x y)
                         (R2 x y))
                    (R3 x y)) :by Hxy)
    (have <b2> (R3 x y) :by (p/and-elim-right% <b1>))
    (have <b3> (R1 x y) :by (p/and-elim-left% (p/and-elim-left% <b1>)))
    (have <b4> (R2 x y) :by (p/and-elim-right% (p/and-elim-left% <b1>)))
    (have <b> _ :by (p/and-intro% <b3> (p/and-intro% <b4> <b2>))))
  (have <c> _ :by (p/and-intro% <a> <b>))
  (qed <c>))

(defthm rinter-assoc-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (rinter T U (rinter T U R1 R2) R3)
         (rinter T U R1 (rinter T U R2 R3))))

(proof rinter-assoc-sym
    :script
  (have <a> (releq T U
                   (rinter T U R1 (rinter T U R2 R3))
                   (rinter T U (rinter T U R1 R2) R3))
        :by (rinter-assoc T U R1 R2 R3))
  (have <b> _ :by ((rel/releq-sym T U
                                   (rinter T U R1 (rinter T U R2 R3))
                                   (rinter T U (rinter T U R1 R2) R3))
                   <a>))
  (qed <b>))

(defthm dist-runion-rinter
  "Distributivity of union over intersection."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (runion T U R1 (rinter T U R2 R3))
         (rinter T U (runion T U R1 R2) (runion T U R1 R3))))

(proof dist-runion-rinter
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((runion T U R1 (rinter T U R2 R3)) x y)]
    (have <a> (or (R1 x y)
                  (and (R2 x y)
                       (R3 x y))) :by Hxy)
    (assume [H1 (R1 x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-left% H1 (R2 x y)))
      (have <b2> (or (R1 x y)
                     (R3 x y))
            :by (p/or-intro-left% H1 (R3 x y)))
      (have <b> _ :by (p/and-intro% <b1> <b2>)))
    (assume [H2 (and (R2 x y)
                     (R3 x y))]
      (have <c1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-right% (R1 x y)
                                   (p/and-elim-left% H2)))
      (have <c2> (or (R1 x y)
                     (R3 x y))
            :by (p/or-intro-right% (R1 x y)
                                   (p/and-elim-right% H2)))
      (have <c> _ :by (p/and-intro% <c1> <c2>)))
    (have <d> ((rinter T U (runion T U R1 R2) (runion T U R1 R3)) x y)
          :by (p/or-elim% <a>
                          ((rinter T U (runion T U R1 R2) (runion T U R1 R3)) x y)
                          <b> <c>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((rinter T U (runion T U R1 R2) (runion T U R1 R3)) x y)]
    (have <e> (or (R1 x y)
                  (R2 x y))
          :by (p/and-elim-left% Hxy))
    (have <f> (or (R1 x y)
                  (R3 x y))
          :by (p/and-elim-right% Hxy))
    (assume [H1 (R1 x y)]
      (have <g> (or (R1 x y)
                    (and (R2 x y)
                         (R3 x y)))
            :by (p/or-intro-left% H1 (and (R2 x y)
                                          (R3 x y)))))  
    (assume [H2 (R2 x y)]
      (assume [H3 (R1 x y)]
        (have <h> (or (R1 x y)
                      (and (R2 x y)
                           (R3 x y)))
              :by (p/or-intro-left% H3 (and (R2 x y)
                                            (R3 x y)))))
      (assume [H4 (R3 x y)]
        (have <i1> _ :by (p/and-intro% H2 H4))
        (have <i> (or (R1 x y)
                      (and (R2 x y)
                           (R3 x y)))
              :by (p/or-intro-right% (R1 x y)
                                     <i1>)))
      (have <j> _ :by (p/or-elim% <f> (or (R1 x y)
                                          (and (R2 x y)
                                               (R3 x y)))
                                  <h> <i>)))
    (have <k> ((runion T U R1 (rinter T U R2 R3)) x y)
          :by (p/or-elim% <e> (or (R1 x y)
                                          (and (R2 x y)
                                               (R3 x y)))
                          <g> <j>)))
  (have <h> _ :by (p/and-intro% <d> <k>))
  (qed <h>))

(defthm dist-runion-rinter-sym
  "Symmetric case of [[dist-runion-rinter]]."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (rinter T U (runion T U R1 R2) (runion T U R1 R3))
         (runion T U R1 (rinter T U R2 R3))))

(proof dist-runion-rinter-sym
    :script
  (have <a> (releq T U
                   (runion T U R1 (rinter T U R2 R3))
                   (rinter T U (runion T U R1 R2) (runion T U R1 R3)))
        :by (dist-runion-rinter T U R1 R2 R3))
  (have <b> _ :by ((rel/releq-sym
                    T U
                    (runion T U R1 (rinter T U R2 R3))
                    (rinter T U (runion T U R1 R2) (runion T U R1 R3))) <a>))
  (qed <b>))

(defthm dist-rinter-runion
  "Distributivity of intersection over union."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (rinter T U R1 (runion T U R2 R3))
         (runion T U (rinter T U R1 R2) (rinter T U R1 R3))))

(proof dist-rinter-runion
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter T U R1 (runion T U R2 R3)) x y)]
    (have <a> (R1 x y) :by (p/and-elim-left% Hxy))
    (have <b> (or (R2 x y)
                  (R3 x y)) :by (p/and-elim-right% Hxy))
    (assume [H1 (R2 x y)]
      (have <c1> (and (R1 x y) (R2 x y))
            :by (p/and-intro% <a> H1))
      (have <c> (or (and (R1 x y) (R2 x y))
                    (and (R1 x y) (R3 x y)))
            :by (p/or-intro-left% <c1> (and (R1 x y) (R3 x y)))))
    (assume [H2 (R3 x y)]
      (have <d1> (and (R1 x y) (R3 x y))
            :by (p/and-intro% <a> H2))
      (have <d> (or (and (R1 x y) (R2 x y))
                    (and (R1 x y) (R3 x y)))
            :by (p/or-intro-right% (and (R1 x y) (R2 x y))
                                   <d1>)))
    (have <e> ((runion T U (rinter T U R1 R2) (rinter T U R1 R3)) x y)
          :by (p/or-elim% <b> (or (and (R1 x y) (R2 x y))
                                  (and (R1 x y) (R3 x y)))
                          <c> <d>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((runion T U (rinter T U R1 R2) (rinter T U R1 R3)) x y)]
    (have <f> (or (and (R1 x y) (R2 x y))
                  (and (R1 x y) (R3 x y))) :by Hxy)
    (assume [H1 (and (R1 x y) (R2 x y))]
      (have <g1> (R1 x y) :by (p/and-elim-left% H1))
      (have <g2> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-left% (p/and-elim-right% H1)
                                  (R3 x y)))
      (have <g> (and (R1 x y)
                     (or (R2 x y)
                         (R3 x y)))
            :by (p/and-intro% <g1> <g2>)))
    (assume [H2 (and (R1 x y) (R3 x y))]
      (have <h1> (R1 x y) :by (p/and-elim-left% H2))
      (have <h2> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-right% (R2 x y)
                                   (p/and-elim-right% H2)))
      (have <h> (and (R1 x y)
                     (or (R2 x y)
                         (R3 x y)))
            :by (p/and-intro% <h1> <h2>)))
    (have <i> ((rinter T U R1 (runion T U R2 R3)) x y)
          :by (p/or-elim% <f> (and (R1 x y)
                                   (or (R2 x y)
                                       (R3 x y)))
                          <g> <h>)))
  (have <j> _ :by (p/and-intro% <e> <i>))
  (qed <j>))


(defthm dist-rinter-runion-sym
  "Symmetric case of [[dist-rinter-runion]]."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq T U
         (runion T U (rinter T U R1 R2) (rinter T U R1 R3))
         (rinter T U R1 (runion T U R2 R3))))

(proof dist-rinter-runion-sym
    :script
  (have <a> (releq T U
                   (rinter T U R1 (runion T U R2 R3))
                   (runion T U (rinter T U R1 R2) (rinter T U R1 R3)))
        :by (dist-rinter-runion T U R1 R2 R3))
  (have <b> _ :by ((rel/releq-sym
                    T U
                    (rinter T U R1 (runion T U R2 R3))
                    (runion T U (rinter T U R1 R2) (rinter T U R1 R3))) <a>))
  (qed <b>))


(definition rdiff
  "Relational difference."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (and (R1 x y)
           (not (R2 x y))))))

(defthm rdiff-empty-right
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U (rdiff T U R (emptyrel T U)) R))

(proof rdiff-empty-right
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff T U R (emptyrel T U)) x y)]
    (have <a> (and (R x y)
                   (not ((emptyrel T U) x y))) :by Hxy)
    (have <b> (R x y) :by (p/and-elim-left% <a>)))
  "Superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <c> (not ((emptyrel T U) x y))
          :by ((rel/emptyrel-prop T U) x y))
    (have <d> (and (R x y)
                   (not ((emptyrel T U) x y)))
          :by (p/and-intro% Hxy <c>)))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))

(defthm rdiff-empty-left
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U (rdiff T U (emptyrel T U) R) (emptyrel T U)))

(proof rdiff-empty-left
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff T U (emptyrel T U) R) x y)]
    (have <a> ((emptyrel T U) x y)
          :by (p/and-elim-left% Hxy)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <b> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <c> _ :by (<b> ((rdiff T U (emptyrel T U) R) x y))))
  (have <d> _ :by (p/and-intro% <a> <c>))
  (qed <d>))

(defthm rdiff-cancel
  [[T :type] [U :type] [R (rel T U)]]
  (releq T U (rdiff T U R R) (emptyrel T U)))

(proof rdiff-cancel
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff T U R R) x y)]
    (have <a1> (R x y) :by (p/and-elim-left% Hxy))
    (have <a2> (not (R x y)) :by (p/and-elim-right% Hxy))
    (have <b> ((emptyrel T U) x y) :by (<a2> <a1>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <c> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <d> _ :by (<c> ((rdiff T U R R) x y))))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))


(definition rcomplement
  "The complement of relation `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (not (R x y)))))

(defthm rcomp-full-empty
  [[T :type] [U :type]]
  (releq T U
         (rcomplement T U (fullrel T U))
         (emptyrel T U)))

(proof rcomp-full-empty
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rcomplement T U (fullrel T U)) x y)]
    (have <a> (not ((fullrel T U) x y)) :by Hxy)
    (have <b> p/absurd :by (<a> ((rel/fullrel-prop T U) x y))))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <c> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <d> _ :by (<c> ((rcomplement T U (fullrel T U)) x y))))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))

(defthm rcomp-empty-full
  [[T :type] [U :type]]
  (releq T U
         (rcomplement T U (emptyrel T U))
         (fullrel T U)))

(proof rcomp-empty-full
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rcomplement T U (emptyrel T U)) x y)]
    (have <a> ((fullrel T U) x y)
          :by ((rel/fullrel-prop T U) x y)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((fullrel T U) x y)]
    (have <b> (not ((emptyrel T U) x y))
          :by ((rel/emptyrel-prop T U) x y)))
  (have <c> _ :by (p/and-intro% <a> <b>))
  (qed <c>))


(definition restrict-dom
  "Restriction of domain of relation `R` to
the subset `s`."
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [x T]
    (lambda [y U]
      (and (elem T x s)
           (R x y)))))

(definition subtract-dom
  "Subtraction of set `s` from the domain of relation `R`"
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [x T]
    (lambda [y U]
      (and (not (elem T x s))
           (R x y)))))

(definition restrict-ran
  "Restriction of range of relation `R` to
the subset `s`."
  [[T :type] [U :type] [R (rel T U)] [s (set U)]]
  (lambda [x T]
    (lambda [y U]
      (and (elem U y s)
           (R x y)))))

(definition subtract-ran
  "Subtraction of set `s` from the range of relation `R`"
  [[T :type] [U :type] [R (rel T U)] [s (set U)]]
  (lambda [x T]
    (lambda [y U]
      (and (not (elem U y s))
           (R x y)))))

(definition rimage
  "Relational image of set `s` for relation `R`."
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [y U]
    (exists [x T]
      (and (elem T x s)
           (R x y)))))

(definition rinverse
  "The relational inverse of `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [y U]
    (lambda [x T]
      (R x y))))

(defthm rinverse-prop
  [[T :type] [U :type] [R (rel T U)] [x T] [y U]]
  (==> (R x y)
       ((rinverse T U R) y x)))

(proof rinverse-prop
    :script
  (assume [H (R x y)]
    (have <a> ((rinverse T U R) y x) :by H)
    (qed <a>)))




