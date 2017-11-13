(ns latte-sets.ralgebra
  "The relation algebra operators."

  (:refer-clojure :exclude [and or not set complement])

  (:require [latte.core :as latte
             :refer [definition defthm defaxiom defnotation
                     forall lambda defimplicit
                     assume have pose qed proof lambda forall]]
 
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as sets
             :refer [set elem subset seteq set-equal emptyset fullset]]

            [latte-sets.algebra :as alg
             :refer [union inter diff]]

            [latte-sets.rel :as rel
             :refer [rel dom ran subrel releq rel-equal emptyrel fullrel
                     fetch-rel-type]]))

(definition runion-def
  "Relational union."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (or (R1 x y)
          (R2 x y)))))

(defimplicit runion
  "`(runion R1 R2)` is the relational union of `R1` and `R2`, cf. [[union-def]]."
  [def-env ctx [R1 R1-ty] [R2 R2-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R1-ty)]
    (list #'runion-def T U R1 R2)))

(defthm runion-idem
  [[T :type] [U :type] [R (rel T U)]]
  (releq (runion R R) R))

(proof 'runion-idem
    :script
  "We first prove that `R`∪`R`⊆`R`."
  (assume [x T
           y U
           Hxy ((runion R R) x y)]
    (have <a> (or (R x y)
                  (R x y)) :by Hxy)
    (assume [Hor (R x y)]
      (have <b> (R x y) :by Hor))
    (have <c> (R x y)
          :by (p/or-elim <a> (R x y) <b> <b>)))
  "We next prove that `R`⊆ `R`∪`R`"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <d> (or (R x y)
                  (R x y))
          :by (p/or-intro-left Hxy (R x y))))
  (qed (p/and-intro <c> <d>)))

(defthm runion-empty
  [[T :type] [U :type] [R (rel T U)]]
  (releq (runion R (emptyrel T U)) R))

(proof 'runion-empty
    :script
  "subset case"
  (assume [x T
           y U
           Hxy ((runion R (emptyrel T U)) x y)]
    (have <a> (or (R x y)
                  ((emptyrel T U) x y)) :by Hxy)
    (assume [H1 (R x y)]
      (have <b> (R x y) :by H1))
    (assume [H2 ((emptyrel T U) x y)]
      (have <c> p/absurd :by H2)
      (have <d> (R x y) :by (<c> (R x y))))
    (have <e> _ :by (p/or-elim <a> (R x y) <b> <d>)))
  "superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <f> (or (R x y)
                  ((emptyrel T U) x y))
          :by (p/or-intro-left Hxy ((emptyrel T U) x y))))
  (qed (p/and-intro <e> <f>)))

(defthm runion-commute
  "Relational union commutes."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (releq (runion R1 R2)
         (runion R2 R1)))

(proof 'runion-commute :script
  (assume [x T
           y U
           H ((runion R1 R2) x y)]
    (have <a1> (or (R1 x y)
                   (R2 x y)) :by H)
    (have <a> _ :by (p/or-sym <a1>)))
  (assume [x T
           y U
           H ((runion R2 R1) x y)]
    (have <b1> (or (R2 x y)
                   (R1 x y)) :by H)
    (have <b> _
          :by (p/or-sym <b1>)))
  (qed (p/and-intro <a> <b>)))

(defthm runion-assoc
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (runion R1 (runion R2 R3))
         (runion (runion R1 R2) R3)))

(proof 'runion-assoc
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((runion R1 (runion R2 R3)) x y)]
    (have <a> (or (R1 x y)
                  ((runion R2 R3) x y)) :by Hxy)
    (assume [H1 (R1 x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-left H1 (R2 x y)))
      (have <b> (or (or (R1 x y)
                        (R2 x y))
                    (R3 x y))
            :by (p/or-intro-left <b1> (R3 x y))))
    (assume [H2 ((runion R2 R3) x y)]
      (have <c1> (or (R2 x y)
                     (R3 x y)) :by H2)
      (assume [H3 (R2 x y)]
        (have <d1> (or (R1 x y)
                       (R2 x y))
              :by (p/or-intro-right (R1 x y) H3))
        (have <d> (or (or (R1 x y)
                          (R2 x y))
                      (R3 x y))
              :by (p/or-intro-left <d1> (R3 x y))))
      (assume [H3 (R3 x y)]
        (have <e> (or (or (R1 x y)
                          (R2 x y))
                      (R3 x y))
              :by (p/or-intro-right (or (R1 x y)
                                        (R2 x y))
                                    H3)))
      (have <c> _ :by (p/or-elim <c1> (or (or (R1 x y)
                                              (R2 x y))
                                          (R3 x y))
                                 <d> <e>)))
    (have <f> ((runion (runion R1 R2) R3) x y)
          :by (p/or-elim <a> (or (or (R1 x y)
                                     (R2 x y))
                                 (R3 x y))
                         <b> <c>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((runion (runion R1 R2) R3) x y)]
    (have <g> (or ((runion R1 R2) x y)
                  (R3 x y)) :by Hxy)
    (assume [H1 ((runion R1 R2) x y)]
      (have <h1> (or (R1 x y)
                     (R2 x y)) :by H1)
      (assume [H2 (R1 x y)]
        (have <i> (or (R1 x y)
                      (or (R2 x y)
                          (R3 x y)))
              :by (p/or-intro-left H2 (or (R2 x y)
                          (R3 x y)))))
      (assume [H3 (R2 x y)]
        (have <j1> (or (R2 x y)
                       (R3 x y))
              :by (p/or-intro-left H3 (R3 x y)))
        (have <j> (or (R1 x y)
                      (or (R2 x y)
                          (R3 x y)))
              :by (p/or-intro-right (R1 x y) <j1>)))
      (have <h> _ :by (p/or-elim <h1> (or (R1 x y)
                                          (or (R2 x y)
                                              (R3 x y)))
                                 <i> <j>)))
    (assume [H2 (R3 x y)]
      (have <k1> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-right (R2 x y) H2))
      (have <k> (or (R1 x y)
                    (or (R2 x y)
                        (R3 x y)))
            :by (p/or-intro-right (R1 x y) <k1>)))
    (have <l> ((runion R1 (runion R2 R3)) x y)
          :by (p/or-elim <g> (or (R1 x y)
                                 (or (R2 x y)
                                     (R3 x y)))
                         <h> <k>)))
  (qed (p/and-intro <f> <l>)))

(defthm runion-assoc-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (runion (runion R1 R2) R3)
         (runion R1 (runion R2 R3))))

(proof 'runion-assoc-sym
    :script
  (have <a> (releq (runion R1 (runion R2 R3))
                   (runion (runion R1 R2) R3))
        :by (runion-assoc T U R1 R2 R3))
  (have <b> _ :by ((rel/releq-sym (runion R1 (runion R2 R3))
                                  (runion (runion R1 R2) R3))
                   <a>))
  (qed <b>))

(defthm runion-dom
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (seteq (dom (runion R1 R2))
         (alg/union (dom R1) (dom R2))))

(proof 'runion-dom
    :script
  "Subset case"
  (assume [x T
           Hx (elem x (dom (runion R1 R2)))]
    (have <a> (exists [y U] ((runion R1 R2) x y))
          :by Hx)
    (assume [y U
             Hy ((runion R1 R2) x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y)) :by Hy)
      (assume [HR1 (R1 x y)]
        (have <c1> (exists [y U] (R1 x y))
              :by ((q/ex-intro (lambda [k U] (R1 x k)) y)
                   HR1))
        (have <c2> (elem x (dom R1)) :by <c1>)
        (have <c3> (or (elem x (dom R1))
                       (elem x (dom R2)))
              :by (p/or-intro-left <c2> (elem x (dom R2))))
        (have <c> (elem x (alg/union (dom R1) (dom R2))) :by <c3>))
      (assume [HR2 (R2 x y)]
        (have <d1> (exists [y U] (R2 x y))
              :by ((q/ex-intro (lambda [k U] (R2 x k)) y)
                   HR2))
        (have <d2> (elem x (dom R2)) :by <d1>)
        (have <d3> (or (elem x (dom R1))
                       (elem x (dom R2)))
              :by (p/or-intro-right (elem x (dom R1)) <d2>))
        (have <d> (elem x (alg/union (dom R1) (dom R2))) :by <d3>))
      (have <e> _ :by (p/or-elim <b1> 
                                 (elem x (alg/union (dom R1) (dom R2)))
                                 <c> <d>)))
    (have <f> _ :by ((q/ex-elim (lambda [k U]
                                        ((runion R1 R2) x k))
                                (elem x (alg/union (dom R1) (dom R2))))
                     <a> <e>)))
  "Supset case"
  (assume [x T
           Hx (elem x (alg/union (dom R1) (dom R2)))]
    (have <g> (or (elem x (dom R1))
                  (elem x (dom R2))) :by Hx)
    (assume [HR1 (elem x (dom R1))]
      (have <h> (exists [y U] (R1 x y)) :by HR1)
      (assume [y U
               Hy (R1 x y)]
        (have <i1> (or (R1 x y) (R2 x y))
              :by (p/or-intro-left Hy (R2 x y)))
        (have <i2> ((runion R1 R2) x y) :by <i1>)
        (have <i> (elem x (dom (runion R1 R2)))
              :by ((q/ex-intro (lambda [k U]
                                       ((runion R1 R2) x k))
                               y)
                   <i2>)))
      (have <j> _ :by ((q/ex-elim (lambda [k U] (R1 x k))
                                  (elem x (dom (runion R1 R2))))
                       <h> <i>)))
    (assume [HR2 (elem x (dom R2))]
      (have <k> (exists [y U] (R2 x y)) :by HR2)
      (assume [y U
               Hy (R2 x y)]
        (have <l1> (or (R1 x y) (R2 x y))
              :by (p/or-intro-right (R1 x y) Hy))
        (have <l2> ((runion R1 R2) x y) :by <l1>)
        (have <l> (elem x (dom (runion R1 R2)))
              :by ((q/ex-intro (lambda [k U]
                                       ((runion R1 R2) x k))
                               y)
                   <l2>)))
      (have <m> _ :by ((q/ex-elim (lambda [k U] (R2 x k))
                                  (elem x (dom (runion R1 R2))))
                       <k> <l>)))
    (have <n> _ :by (p/or-elim <g> (elem x (dom (runion R1 R2)))
                               <j> <m>)))
  (qed (p/and-intro <f> <n>)))


(defthm runion-ran
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (seteq (ran (runion R1 R2))
         (alg/union (ran R1) (ran R2))))

(proof 'runion-ran
    :script
  "Subset case"
  (assume [y U
           Hy (elem y (ran (runion R1 R2)))]
    (have <a> (exists [x T] ((runion R1 R2) x y))
          :by Hy)
    (assume [x T
             Hx ((runion R1 R2) x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y)) :by Hx)
      (assume [HR1 (R1 x y)]
        (have <c1> (exists [x T] (R1 x y))
              :by ((q/ex-intro (lambda [k T] (R1 k y)) x)
                   HR1))
        (have <c2> (elem y (ran R1)) :by <c1>)
        (have <c3> (or (elem y (ran R1))
                       (elem y (ran R2)))
              :by (p/or-intro-left <c2> (elem y (ran R2))))
        (have <c> (elem y (alg/union (ran R1) (ran R2))) :by <c3>))
      (assume [HR2 (R2 x y)]
        (have <d1> (exists [x T] (R2 x y))
              :by ((q/ex-intro (lambda [k T] (R2 k y)) x)
                   HR2))
        (have <d2> (elem y (ran R2)) :by <d1>)
        (have <d3> (or (elem y (ran R1))
                       (elem y (ran R2)))
              :by (p/or-intro-right (elem y (ran R1)) <d2>))
        (have <d> (elem y (alg/union (ran R1) (ran R2))) :by <d3>))
      (have <e> _ :by (p/or-elim <b1> 
                                 (elem y (alg/union (ran R1) (ran R2)))
                                  <c> <d>)))
    (have <f> _ :by ((q/ex-elim (lambda [k T]
                                        ((runion R1 R2) k y))
                                (elem y (alg/union (ran R1) (ran R2))))
                     <a> <e>)))

  "Supset case"
   (assume [y U
            Hy (elem y (alg/union (ran R1) (ran R2)))]
     (have <g> (or (elem y (ran R1))
                   (elem y (ran R2))) :by Hy)
     (assume [HR1 (elem y (ran R1))]
       (have <h> (exists [x T] (R1 x y)) :by HR1)
       (assume [x T
                Hx (R1 x y)]
         (have <i1> (or (R1 x y) (R2 x y))
               :by (p/or-intro-left Hx (R2 x y)))
         (have <i2> ((runion R1 R2) x y) :by <i1>)
         (have <i> (elem y (ran (runion R1 R2)))
               :by ((q/ex-intro (lambda [k T]
                                        ((runion R1 R2) k y))
                                x)
                    <i2>)))
       (have <j> _ :by ((q/ex-elim (lambda [k T] (R1 k y))
                                   (elem y (ran (runion R1 R2))))
                        <h> <i>)))
     (assume [HR2 (elem y (ran R2))]
       (have <k> (exists [x T] (R2 x y)) :by HR2)
       (assume [x T
                Hx (R2 x y)]
         (have <l1> (or (R1 x y) (R2 x y))
               :by (p/or-intro-right (R1 x y) Hx))
         (have <l2> ((runion R1 R2) x y) :by <l1>)
         (have <l> (elem y (ran (runion R1 R2)))
               :by ((q/ex-intro (lambda [k T]
                                        ((runion R1 R2) k y))
                                x)
                    <l2>)))
       (have <m> _ :by ((q/ex-elim (lambda [k T] (R2 k y))
                                   (elem y (ran (runion R1 R2))))
                        <k> <l>)))
     (have <n> _ :by (p/or-elim <g> (elem y (ran (runion R1 R2)))
                                <j> <m>)))
   (qed (p/and-intro <f> <n>)))


(definition rinter-def
  "Relational intersection."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (and (R1 x y)
           (R2 x y)))))

(defimplicit rinter
  "`(rinter R1 R2)` is the relational intersection of `R1` and `R2`, cf. [[rinter-def]]."
  [def-env ctx [R1 R1-ty] [R2 R2-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R1-ty)]
    (list #'rinter-def T U R1 R2)))

(defthm rinter-elim-left
  "Elimination rule for intersection (left operand)."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [x T] [y U]]
  (==> ((rinter R1 R2) x y)
       (R1 x y)))

(proof 'rinter-elim-left
    :script
  (assume [H ((rinter R1 R2) x y)]
    (have <a> (R1 x y) :by (p/and-elim-left H)))
  (qed <a>))

(defthm rinter-elim-right
  "Elimination rule for intersection (right operand)."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [x T] [y U]]
  (==> ((rinter R1 R2) x y)
       (R2 x y)))

(proof 'rinter-elim-right
    :script
  (assume [H ((rinter R1 R2) x y)]
    (have <a> (R2 x y) :by (p/and-elim-right H)))
  (qed <a>))


(defthm rinter-idem
  [[T :type] [U :type] [R (rel T U)]]
  (releq (rinter R R) R))

(proof 'rinter-idem
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter R R) x y)]
    (have <a> (and (R x y)
                   (R x y)) :by Hxy)
    (have <b> (R x y) :by (p/and-elim-left <a>)))
  "Superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <c> (and (R x y)
                   (R x y))
          :by (p/and-intro Hxy Hxy)))
  (qed (p/and-intro <b> <c>)))

(defthm rinter-empty
  [[T :type] [U :type] [R (rel T U)]]
  (releq (rinter R (emptyrel T U))
         (emptyrel T U)))

(proof 'rinter-empty
    :script
  "Subset case."
  (assume [x T
           y U
           Hxy ((rinter R (emptyrel T U)) x y)]
    (have <a> ((emptyrel T U) x y)
          :by (p/and-elim-right Hxy)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <b> p/absurd :by Hxy)
    (have <c> _ :by (<b> ((rinter R (emptyrel T U)) x y))))
  (qed (p/and-intro <a> <c>)))

(defthm rinter-commute
  "Relation intersection commutes."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (releq (rinter R1 R2)
         (rinter R2 R1)))

(proof 'rinter-commute
    :script
  (assume [x T
           y U
           Hxy ((rinter R1 R2) x y)]
    (have <a> ((rinter R2 R1) x y)
          :by (p/and-sym Hxy)))
  (assume [x T
           y U
           Hxy ((rinter R2 R1) x y)]
    (have <b> ((rinter R1 R2) x y)
          :by (p/and-sym Hxy)))
  (qed (p/and-intro <a> <b>)))

(defthm rinter-assoc
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (rinter R1 (rinter R2 R3))
         (rinter (rinter R1 R2) R3)))

(proof 'rinter-assoc
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter R1 (rinter R2 R3)) x y)]
    (have <a1> (and (R1 x y)
                    (and (R2 x y)
                         (R3 x y))) :by Hxy)
    (have <a2> (R1 x y) :by (p/and-elim-left <a1>))
    (have <a3> (R2 x y) :by (p/and-elim-left (p/and-elim-right <a1>)))
    (have <a4> (R3 x y) :by (p/and-elim-right (p/and-elim-right <a1>)))
    (have <a> _ :by (p/and-intro (p/and-intro <a2> <a3>) <a4>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((rinter (rinter R1 R2) R3) x y)]
    (have <b1> (and (and (R1 x y)
                         (R2 x y))
                    (R3 x y)) :by Hxy)
    (have <b2> (R3 x y) :by (p/and-elim-right <b1>))
    (have <b3> (R1 x y) :by (p/and-elim-left (p/and-elim-left <b1>)))
    (have <b4> (R2 x y) :by (p/and-elim-right (p/and-elim-left <b1>)))
    (have <b> _ :by (p/and-intro <b3> (p/and-intro <b4> <b2>))))
  (qed (p/and-intro <a> <b>)))

(defthm rinter-assoc-sym
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (rinter (rinter R1 R2) R3)
         (rinter R1 (rinter R2 R3))))

(proof 'rinter-assoc-sym
    :script
  (have <a> (releq (rinter R1 (rinter R2 R3))
                   (rinter (rinter R1 R2) R3))
        :by (rinter-assoc T U R1 R2 R3))
  (qed ((rel/releq-sym (rinter R1 (rinter R2 R3))
                       (rinter (rinter R1 R2) R3))
        <a>)))

(defthm dist-runion-rinter
  "Distributivity of union over intersection."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (runion R1 (rinter R2 R3))
         (rinter (runion R1 R2) (runion R1 R3))))

(proof 'dist-runion-rinter
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((runion R1 (rinter R2 R3)) x y)]
    (have <a> (or (R1 x y)
                  (and (R2 x y)
                       (R3 x y))) :by Hxy)
    (assume [H1 (R1 x y)]
      (have <b1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-left H1 (R2 x y)))
      (have <b2> (or (R1 x y)
                     (R3 x y))
            :by (p/or-intro-left H1 (R3 x y)))
      (have <b> _ :by (p/and-intro <b1> <b2>)))
    (assume [H2 (and (R2 x y)
                     (R3 x y))]
      (have <c1> (or (R1 x y)
                     (R2 x y))
            :by (p/or-intro-right (R1 x y)
                                  (p/and-elim-left H2)))
      (have <c2> (or (R1 x y)
                     (R3 x y))
            :by (p/or-intro-right (R1 x y)
                                   (p/and-elim-right H2)))
      (have <c> _ :by (p/and-intro <c1> <c2>)))
    (have <d> ((rinter (runion R1 R2) (runion R1 R3)) x y)
          :by (p/or-elim <a>
                         ((rinter (runion R1 R2) (runion R1 R3)) x y)
                         <b> <c>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((rinter (runion R1 R2) (runion R1 R3)) x y)]
    (have <e> (or (R1 x y)
                  (R2 x y))
          :by (p/and-elim-left Hxy))
    (have <f> (or (R1 x y)
                  (R3 x y))
          :by (p/and-elim-right Hxy))
    (assume [H1 (R1 x y)]
      (have <g> (or (R1 x y)
                    (and (R2 x y)
                         (R3 x y)))
            :by (p/or-intro-left H1 (and (R2 x y)
                                         (R3 x y)))))  
    (assume [H2 (R2 x y)]
      (assume [H3 (R1 x y)]
        (have <h> (or (R1 x y)
                      (and (R2 x y)
                           (R3 x y)))
              :by (p/or-intro-left H3 (and (R2 x y)
                                           (R3 x y)))))
      (assume [H4 (R3 x y)]
        (have <i1> _ :by (p/and-intro H2 H4))
        (have <i> (or (R1 x y)
                      (and (R2 x y)
                           (R3 x y)))
              :by (p/or-intro-right (R1 x y)
                                    <i1>)))
      (have <j> _ :by (p/or-elim <f> (or (R1 x y)
                                         (and (R2 x y)
                                              (R3 x y)))
                                 <h> <i>)))
    (have <k> ((runion R1 (rinter R2 R3)) x y)
          :by (p/or-elim <e> (or (R1 x y)
                                 (and (R2 x y)
                                      (R3 x y)))
                         <g> <j>)))
  (qed (p/and-intro <d> <k>)))

(defthm dist-runion-rinter-sym
  "Symmetric case of [[dist-runion-rinter]]."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (rinter (runion R1 R2) (runion R1 R3))
         (runion R1 (rinter R2 R3))))

(proof 'dist-runion-rinter-sym
    :script
  (have <a> (releq (runion R1 (rinter R2 R3))
                   (rinter (runion R1 R2) (runion R1 R3)))
        :by (dist-runion-rinter T U R1 R2 R3))
  (qed ((rel/releq-sym (runion R1 (rinter R2 R3))
                       (rinter (runion R1 R2) (runion R1 R3))) <a>)))

(defthm dist-rinter-runion
  "Distributivity of intersection over union."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (rinter R1 (runion R2 R3))
         (runion (rinter R1 R2) (rinter R1 R3))))

(proof 'dist-rinter-runion
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rinter R1 (runion R2 R3)) x y)]
    (have <a> (R1 x y) :by (p/and-elim-left Hxy))
    (have <b> (or (R2 x y)
                  (R3 x y)) :by (p/and-elim-right Hxy))
    (assume [H1 (R2 x y)]
      (have <c1> (and (R1 x y) (R2 x y))
            :by (p/and-intro <a> H1))
      (have <c> (or (and (R1 x y) (R2 x y))
                    (and (R1 x y) (R3 x y)))
            :by (p/or-intro-left <c1> (and (R1 x y) (R3 x y)))))
    (assume [H2 (R3 x y)]
      (have <d1> (and (R1 x y) (R3 x y))
            :by (p/and-intro <a> H2))
      (have <d> (or (and (R1 x y) (R2 x y))
                    (and (R1 x y) (R3 x y)))
            :by (p/or-intro-right(and (R1 x y) (R2 x y))
                                   <d1>)))
    (have <e> ((runion (rinter R1 R2) (rinter R1 R3)) x y)
          :by (p/or-elim <b> (or (and (R1 x y) (R2 x y))
                                 (and (R1 x y) (R3 x y)))
                         <c> <d>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((runion (rinter R1 R2) (rinter R1 R3)) x y)]
    (have <f> (or (and (R1 x y) (R2 x y))
                  (and (R1 x y) (R3 x y))) :by Hxy)
    (assume [H1 (and (R1 x y) (R2 x y))]
      (have <g1> (R1 x y) :by (p/and-elim-left H1))
      (have <g2> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-left (p/and-elim-right H1)
                                  (R3 x y)))
      (have <g> (and (R1 x y)
                     (or (R2 x y)
                         (R3 x y)))
            :by (p/and-intro <g1> <g2>)))
    (assume [H2 (and (R1 x y) (R3 x y))]
      (have <h1> (R1 x y) :by (p/and-elim-left H2))
      (have <h2> (or (R2 x y)
                     (R3 x y))
            :by (p/or-intro-right (R2 x y)
                                  (p/and-elim-right H2)))
      (have <h> (and (R1 x y)
                     (or (R2 x y)
                         (R3 x y)))
            :by (p/and-intro <h1> <h2>)))
    (have <i> ((rinter R1 (runion R2 R3)) x y)
          :by (p/or-elim <f> (and (R1 x y)
                                  (or (R2 x y)
                                      (R3 x y)))
                         <g> <h>)))
  (qed (p/and-intro <e> <i>)))

(defthm dist-rinter-runion-sym
  "Symmetric case of [[dist-rinter-runion]]."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)] [R3 (rel T U)]]
  (releq (runion (rinter R1 R2) (rinter R1 R3))
         (rinter R1 (runion R2 R3))))

(proof 'dist-rinter-runion-sym
    :script
  (have <a> (releq(rinter R1 (runion R2 R3))
                   (runion (rinter R1 R2) (rinter R1 R3)))
        :by (dist-rinter-runion T U R1 R2 R3))
  (qed ((rel/releq-sym
         (rinter R1 (runion R2 R3))
         (runion (rinter R1 R2) (rinter R1 R3))) <a>)))


(definition rdiff-def
  "Relational difference."
  [[T :type] [U :type] [R1 (rel T U)] [R2 (rel T U)]]
  (lambda [x T]
    (lambda [y U]
      (and (R1 x y)
           (not (R2 x y))))))

(defimplicit rdiff
  "`(rdiff s1 s2)` is the relational difference of `s1` and `s2`, cf. [[rdiff-def]]."
  [def-env ctx [R1 R1-ty] [R2 R2-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R1-ty)]
    (list #'rdiff-def T U R1 R2)))

(defthm rdiff-empty-right
  [[T :type] [U :type] [R (rel T U)]]
  (releq (rdiff R (emptyrel T U)) R))

(proof 'rdiff-empty-right
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff R (emptyrel T U)) x y)]
    (have <a> (and (R x y)
                   (not ((emptyrel T U) x y))) :by Hxy)
    (have <b> (R x y) :by (p/and-elim-left <a>)))
  "Superset case"
  (assume [x T
           y U
           Hxy (R x y)]
    (have <c> (not ((emptyrel T U) x y))
          :by ((rel/emptyrel-prop T U) x y))
    (have <d> (and (R x y)
                   (not ((emptyrel T U) x y)))
          :by (p/and-intro Hxy <c>)))
  (qed (p/and-intro <b> <d>)))

(defthm rdiff-empty-left
  [[T :type] [U :type] [R (rel T U)]]
  (releq (rdiff (emptyrel T U) R) (emptyrel T U)))

(proof 'rdiff-empty-left
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff (emptyrel T U) R) x y)]
    (have <a> ((emptyrel T U) x y)
          :by (p/and-elim-left Hxy)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <b> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <c> _ :by (<b> ((rdiff (emptyrel T U) R) x y))))
  (qed (p/and-intro <a> <c>)))


(defthm rdiff-cancel
  [[T :type] [U :type] [R (rel T U)]]
  (releq (rdiff R R) (emptyrel T U)))

(proof 'rdiff-cancel
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rdiff R R) x y)]
    (have <a1> (R x y) :by (p/and-elim-left Hxy))
    (have <a2> (not (R x y)) :by (p/and-elim-right Hxy))
    (have <b> ((emptyrel T U) x y) :by (<a2> <a1>)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <c> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <d> _ :by (<c> ((rdiff R R) x y))))
  (qed (p/and-intro <b> <d>)))


(definition rcomplement-def
  "The complement of relation `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [x T]
    (lambda [y U]
            (not (R x y)))))

(defimplicit rcomplement
  "`(rcomplement R)` is the relational complement of `R`, cf. [[rcomplement-def]]."
  [def-env ctx [R R-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'rcomplement-def T U R)))

(defthm rcomp-full-empty
  [[T :type] [U :type]]
  (releq (rcomplement (fullrel T U))
         (emptyrel T U)))

(proof 'rcomp-full-empty
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rcomplement (fullrel T U)) x y)]
    (have <a> (not ((fullrel T U) x y)) :by Hxy)
    (have <b> p/absurd :by (<a> ((rel/fullrel-prop T U) x y))))
  "Superset case"
  (assume [x T
           y U
           Hxy ((emptyrel T U) x y)]
    (have <c> p/absurd :by (((rel/emptyrel-prop T U) x y) Hxy))
    (have <d> _ :by (<c> ((rcomplement (fullrel T U)) x y))))
  (qed (p/and-intro <b> <d>)))

(defthm rcomp-empty-full
  [[T :type] [U :type]]
  (releq (rcomplement (emptyrel T U))
         (fullrel T U)))

(proof 'rcomp-empty-full
    :script
  "Subset case"
  (assume [x T
           y U
           Hxy ((rcomplement (emptyrel T U)) x y)]
    (have <a> ((fullrel T U) x y)
          :by ((rel/fullrel-prop T U) x y)))
  "Superset case"
  (assume [x T
           y U
           Hxy ((fullrel T U) x y)]
    (have <b> (not ((emptyrel T U) x y))
          :by ((rel/emptyrel-prop T U) x y)))
  (qed (p/and-intro <a> <b>)))


(definition restrict-dom-def
  "Restriction of domain of relation `R` to
the subset `s`."
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [x T]
    (lambda [y U]
      (and (elem x s)
           (R x y)))))

(defimplicit restrict-dom
  "`(restrict-dom R s)` is the restriction of relation `R` to domain `s`, cf. [[restrict-dom-def]]."
  [def-env ctx [R R-ty] [s s-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'restrict-dom-def T U R s)))

(defthm restrict-dom-dom
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (seteq (dom (restrict-dom R s))
         (inter s (dom R))))

(proof 'restrict-dom-dom
    :script
  "Subset case"
  (assume [x T
           Hx (elem x (dom (restrict-dom R s)))]
    (assume [y U
             Hy ((restrict-dom R s) x y)]
      (have <a> (elem x s) :by (p/and-elim-left Hy))
      (have <b1> (R x y) :by (p/and-elim-right Hy))
      (have <b> (exists [z U] (R x z))
            :by ((q/ex-intro (lambda [z U] (R x z)) y)
                 <b1>))
      (have <c> (elem x (inter s (dom R)))
            :by (p/and-intro <a> <b>)))
    (have <d> _ :by
          ((q/ex-elim (lambda [z U]
                              ((restrict-dom R s) x z))
                      (elem x (inter s (dom R))))
           Hx <c>)))
  "Superset case"
  (assume [x T
           Hx (elem x (inter s (dom R)))]
    (have <e> (and (elem x s)
                   (exists [y U] (R x y))) :by Hx)
    (assume [y U
             Hy (R x y)]
      (have <f1> ((restrict-dom R s) x y)
            :by (p/and-intro (p/and-elim-left <e>)
                             Hy))
      (have <f> (exists [z U] ((restrict-dom R s) x z))
            :by ((q/ex-intro (lambda [z U]
                                     ((restrict-dom R s) x z)) y)
                 <f1>)))
    (have <g> _ :by ((q/ex-elim (lambda [z U] (R x z))
                                (exists [y U]
                                  ((restrict-dom R s) x y)))
                     (p/and-elim-right <e>)
                     <f>))
    (have <h> (elem x (dom (restrict-dom R s)))
          :by <g>))
  (qed (p/and-intro <d> <h>)))

(definition subtract-dom-def
  "Subtraction (or anti-restriction) of set `s` from the domain of relation `R`"
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [x T]
    (lambda [y U]
      (and (not (elem x s))
           (R x y)))))

(defimplicit subtract-dom
  "`(subtract-dom R s)` is the anti-restriction of relation `R` wrt. domain `s`, cf. [[subtract-dom-def]]."
  [def-env ctx [R R-ty] [s s-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'subtract-dom-def T U R s)))

(definition restrict-ran-def
  "Restriction of range of relation `R` to
the subset `s`."
  [[T :type] [U :type] [R (rel T U)] [s (set U)]]
  (lambda [x T]
    (lambda [y U]
      (and (elem y s)
           (R x y)))))

(defimplicit restrict-ran
  "`(restrict-ran R s)` is the restriction of relation `R` to range (or codomain) `s`, cf. [[restrict-ran-def]]."
  [def-env ctx [R R-ty] [s s-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'restrict-ran-def T U R s)))

(definition subtract-ran-def
  "Subtraction of set `s` from the range of relation `R`"
  [[T :type] [U :type] [R (rel T U)] [s (set U)]]
  (lambda [x T]
    (lambda [y U]
      (and (not (elem y s))
           (R x y)))))

(defimplicit subtract-ran
  "`(subtract-ran R s)` is the anti-restriction of relation `R` wrt. codomain `s`, cf. [[subtract-ran-def]]."
  [def-env ctx [R R-ty] [s s-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'subtract-ran-def T U R s)))

(definition rimage-def
  "Relational image of set `s` for relation `R`."
  [[T :type] [U :type] [R (rel T U)] [s (set T)]]
  (lambda [y U]
    (exists [x T]
      (and (elem x s)
           (R x y)))))

(defimplicit rimage
  "`(rimage R s)` is the image of set `s` through relation `R`, cf. [[rimage-def]]."
  [def-env ctx [R R-ty] [s s-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'rimage-def T U R s)))

(definition rinverse-def
  "The relational inverse of `R`."
  [[T :type] [U :type] [R (rel T U)]]
  (lambda [y U]
    (lambda [x T]
            (R x y))))

(defimplicit rinverse
  "`(rinverse R)` is the inverse of relation `R`, cf. [[rinverse-def]]."
  [def-env ctx [R R-ty]]
  (let [[T U] (fetch-rel-type def-env ctx R-ty)]
    (list #'rinverse-def T U R)))

(defthm rinverse-prop
  [[T :type] [U :type] [R (rel T U)] [x T] [y U]]
  (==> (R x y)
       ((rinverse R) y x)))

(proof 'rinverse-prop
    :script
  (assume [H (R x y)]
    (have <a> ((rinverse R) y x) :by H))
  (qed <a>))




