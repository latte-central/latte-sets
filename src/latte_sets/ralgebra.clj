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

(comment
(definition inter
  "Set intersection.

`(inter T s1 s2)` is the set `s1`∩`s2`."

  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem T x s1)
         (elem T x s2))))

(defthm inter-elim-left
  "Elimination rule for intersection (left operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem T x (inter T s1 s2))
       (elem T x s1)))

(proof inter-elim-left :script
  (assume [H (elem T x (inter T s1 s2))]
    (have a (elem T x s1) :by (p/and-elim-left% H))
    (qed a)))

(defthm inter-elim-right
  "Elimination rule for intersection (right operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem T x (inter T s1 s2))
       (elem T x s2)))

(proof inter-elim-right :script
  (assume [H (elem T x (inter T s1 s2))]
    (have a (elem T x s2) :by (p/and-elim-right% H))
    (qed a)))

(defthm inter-idem
  [[T :type] [s (set T)]]
  (seteq T
         (inter T s s)
         s))

(proof inter-idem
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (inter T s s))]
    (have <a> (and (elem T x s)
                   (elem T x s)) :by Hx)
    (have <b> (elem T x s) :by (p/and-elim-left% <a>)))
  "Superset case"
  (assume [x T
           Hx (elem T x s)]
    (have <c> (and (elem T x s)
                   (elem T x s))
          :by (p/and-intro% Hx Hx)))
  (have <d> _ :by (p/and-intro% <b> <c>))
  (qed <d>))

(defthm inter-empty
  [[T :type] [s (set T)]]
  (seteq T (inter T s (emptyset T))
         (emptyset T)))

(proof inter-empty
    :script
  "Subset case."
  (assume [x T
           Hx (elem T x (inter T s (emptyset T)))]
    (have <a> (elem T x (emptyset T))
          :by (p/and-elim-right% Hx)))
  "Superset case"
  (assume [x T
           Hx (elem T x (emptyset T))]
    (have <b> p/absurd :by Hx)
    (have <c> _ :by (<b> (elem T x (inter T s (emptyset T))))))
  (have <d> _ :by (p/and-intro% <a> <c>))
  (qed <d>))

(defthm inter-commute
  "Set intersection commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq T
         (inter T s1 s2)
         (inter T s2 s1)))  

(proof inter-commute :script
  (assume [x T
           H (elem T x (inter T s1 s2))]
    (have a (elem T x (inter T s2 s1))
          :by ((p/and-sym (elem T x s1) (elem T x s2)) H)))
  (assume [x T
           H (elem T x (inter T s2 s1))]
    (have b (elem T x (inter T s1 s2))
          :by ((p/and-sym (elem T x s2) (elem T x s1)) H)))
  (have c (seteq T
                 (inter T s1 s2)
                 (inter T s2 s1))
        :by (p/and-intro% a b))
  (qed c))

(defthm inter-assoc
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (inter T s1 (inter T s2 s3))
         (inter T (inter T s1 s2) s3)))

(proof inter-assoc
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (inter T s1 (inter T s2 s3)))]
    (have <a1> (and (elem T x s1)
                    (and (elem T x s2)
                         (elem T x s3))) :by Hx)
    (have <a2> (elem T x s1) :by (p/and-elim-left% <a1>))
    (have <a3> (elem T x s2) :by (p/and-elim-left% (p/and-elim-right% <a1>)))
    (have <a4> (elem T x s3) :by (p/and-elim-right% (p/and-elim-right% <a1>)))
    (have <a> _ :by (p/and-intro% (p/and-intro% <a2> <a3>) <a4>)))
  "Superset case"
  (assume [x T
           Hx (elem T x (inter T (inter T s1 s2) s3))]
    (have <b1> (and (and (elem T x s1)
                         (elem T x s2))
                    (elem T x s3)) :by Hx)
    (have <b2> (elem T x s3) :by (p/and-elim-right% <b1>))
    (have <b3> (elem T x s1) :by (p/and-elim-left% (p/and-elim-left% <b1>)))
    (have <b4> (elem T x s2) :by (p/and-elim-right% (p/and-elim-left% <b1>)))
    (have <b> _ :by (p/and-intro% <b3> (p/and-intro% <b4> <b2>))))
  (have <c> _ :by (p/and-intro% <a> <b>))
  (qed <c>))

(defthm inter-assoc-sym
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (inter T (inter T s1 s2) s3)
         (inter T s1 (inter T s2 s3))))

(proof inter-assoc-sym
    :script
  (have <a> (seteq T
         (inter T s1 (inter T s2 s3))
         (inter T (inter T s1 s2) s3))
        :by (inter-assoc T s1 s2 s3))
  (have <b> _ :by ((sets/seteq-sym T
                                   (inter T s1 (inter T s2 s3))
                                   (inter T (inter T s1 s2) s3))
                   <a>))
  (qed <b>))

(defthm dist-union-inter
  "Distributivity of union over intersection."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (union T s1 (inter T s2 s3))
         (inter T (union T s1 s2) (union T s1 s3))))

(proof dist-union-inter
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (union T s1 (inter T s2 s3)))]
    (have <a> (or (elem T x s1)
                  (and (elem T x s2)
                       (elem T x s3))) :by Hx)
    (assume [H1 (elem T x s1)]
      (have <b1> (or (elem T x s1)
                     (elem T x s2))
            :by (p/or-intro-left% H1 (elem T x s2)))
      (have <b2> (or (elem T x s1)
                     (elem T x s3))
            :by (p/or-intro-left% H1 (elem T x s3)))
      (have <b> _ :by (p/and-intro% <b1> <b2>)))
    (assume [H2 (and (elem T x s2)
                     (elem T x s3))]
      (have <c1> (or (elem T x s1)
                     (elem T x s2))
            :by (p/or-intro-right% (elem T x s1)
                                   (p/and-elim-left% H2)))
      (have <c2> (or (elem T x s1)
                     (elem T x s3))
            :by (p/or-intro-right% (elem T x s1)
                                   (p/and-elim-right% H2)))
      (have <c> _ :by (p/and-intro% <c1> <c2>)))
    (have <d> (elem T x (inter T (union T s1 s2) (union T s1 s3)))
          :by (p/or-elim% <a>
                          (elem T x (inter T (union T s1 s2) (union T s1 s3)))
                          <b> <c>)))
  "Superset case"
  (assume [x T
           Hx (elem T x (inter T (union T s1 s2) (union T s1 s3)))]
    (have <e> (or (elem T x s1)
                  (elem T x s2))
          :by (p/and-elim-left% Hx))
    (have <f> (or (elem T x s1)
                  (elem T x s3))
          :by (p/and-elim-right% Hx))
    (assume [H1 (elem T x s1)]
      (have <g> (or (elem T x s1)
                    (and (elem T x s2)
                         (elem T x s3)))
            :by (p/or-intro-left% H1 (and (elem T x s2)
                                          (elem T x s3)))))  
     (assume [H2 (elem T x s2)]
       (assume [H3 (elem T x s1)]
         (have <h> (or (elem T x s1)
                       (and (elem T x s2)
                            (elem T x s3)))
               :by (p/or-intro-left% H3 (and (elem T x s2)
                                             (elem T x s3)))))
       (assume [H4 (elem T x s3)]
         (have <i1> _ :by (p/and-intro% H2 H4))
         (have <i> (or (elem T x s1)
                       (and (elem T x s2)
                            (elem T x s3)))
               :by (p/or-intro-right% (elem T x s1)
                                      <i1>)))
       (have <j> _ :by (p/or-elim% <f> (or (elem T x s1)
                                           (and (elem T x s2)
                                                (elem T x s3)))
                                   <h> <i>)))
     (have <k> (elem T x (union T s1 (inter T s2 s3)))
           :by (p/or-elim% <e> (or (elem T x s1)
                                   (and (elem T x s2)
                                        (elem T x s3)))
                           <g> <j>)))
  (have <h> _ :by (p/and-intro% <d> <k>))
  (qed <h>))

(defthm dist-union-inter-sym
  "Symmetric case of [[dist-union-inter]]."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (inter T (union T s1 s2) (union T s1 s3))
         (union T s1 (inter T s2 s3))))

(proof dist-union-inter-sym
    :script
  (have <a> (seteq T
                   (union T s1 (inter T s2 s3))
                   (inter T (union T s1 s2) (union T s1 s3)))
        :by (dist-union-inter T s1 s2 s3))
  (have <b> _ :by ((sets/seteq-sym
                    T
                    (union T s1 (inter T s2 s3))
                    (inter T (union T s1 s2) (union T s1 s3))) <a>))
  (qed <b>))

(defthm dist-inter-union
  "Distributivity of intersection over union."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (inter T s1 (union T s2 s3))
         (union T (inter T s1 s2) (inter T s1 s3))))

(proof dist-inter-union
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (inter T s1 (union T s2 s3)))]
    (have <a> (elem T x s1) :by (p/and-elim-left% Hx))
    (have <b> (or (elem T x s2)
                  (elem T x s3)) :by (p/and-elim-right% Hx))
    (assume [H1 (elem T x s2)]
      (have <c1> (and (elem T x s1) (elem T x s2))
            :by (p/and-intro% <a> H1))
      (have <c> (or (and (elem T x s1) (elem T x s2))
                    (and (elem T x s1) (elem T x s3)))
            :by (p/or-intro-left% <c1> (and (elem T x s1) (elem T x s3)))))
    (assume [H2 (elem T x s3)]
      (have <d1> (and (elem T x s1) (elem T x s3))
            :by (p/and-intro% <a> H2))
      (have <d> (or (and (elem T x s1) (elem T x s2))
                    (and (elem T x s1) (elem T x s3)))
            :by (p/or-intro-right% (and (elem T x s1) (elem T x s2))
                                   <d1>)))
    (have <e> (elem T x (union T (inter T s1 s2) (inter T s1 s3)))
          :by (p/or-elim% <b> (or (and (elem T x s1) (elem T x s2))
                                  (and (elem T x s1) (elem T x s3)))
                          <c> <d>)))
  "Superset case"
  (assume [x T
           Hx (elem T x (union T (inter T s1 s2) (inter T s1 s3)))]
    (have <f> (or (and (elem T x s1) (elem T x s2))
                  (and (elem T x s1) (elem T x s3))) :by Hx)
    (assume [H1 (and (elem T x s1) (elem T x s2))]
      (have <g1> (elem T x s1) :by (p/and-elim-left% H1))
      (have <g2> (or (elem T x s2)
                     (elem T x s3))
            :by (p/or-intro-left% (p/and-elim-right% H1)
                                  (elem T x s3)))
      (have <g> (and (elem T x s1)
                     (or (elem T x s2)
                         (elem T x s3)))
            :by (p/and-intro% <g1> <g2>)))
    (assume [H2 (and (elem T x s1) (elem T x s3))]
      (have <h1> (elem T x s1) :by (p/and-elim-left% H2))
      (have <h2> (or (elem T x s2)
                     (elem T x s3))
            :by (p/or-intro-right% (elem T x s2)
                                   (p/and-elim-right% H2)))
      (have <h> (and (elem T x s1)
                     (or (elem T x s2)
                         (elem T x s3)))
            :by (p/and-intro% <h1> <h2>)))
    (have <i> (elem T x (inter T s1 (union T s2 s3)))
          :by (p/or-elim% <f> (and (elem T x s1)
                                   (or (elem T x s2)
                                       (elem T x s3)))
                          <g> <h>)))
  (have <j> _ :by (p/and-intro% <e> <i>))
  (qed <j>))


(defthm dist-inter-union-sym
  "Symmetric case of [[dist-inter-union]]."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (union T (inter T s1 s2) (inter T s1 s3))
         (inter T s1 (union T s2 s3))))

(proof dist-inter-union-sym
    :script
  (have <a> (seteq T
                   (inter T s1 (union T s2 s3))
                   (union T (inter T s1 s2) (inter T s1 s3)))
        :by (dist-inter-union T s1 s2 s3))
  (have <b> _ :by ((sets/seteq-sym
                    T
                    (inter T s1 (union T s2 s3))
                    (union T (inter T s1 s2) (inter T s1 s3))) <a>))
  (qed <b>))


(definition diff
  "Set difference

`(difference T s1 s2)` is the set `s1`∖`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem T x s1)
         (not (elem T x s2)))))

(defthm diff-empty-right
  [[T :type] [s (set T)]]
  (seteq T (diff T s (emptyset T)) s))

(proof diff-empty-right
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (diff T s (emptyset T)))]
    (have <a> (and (elem T x s)
                   (not (elem T x (emptyset T)))) :by Hx)
    (have <b> (elem T x s) :by (p/and-elim-left% <a>)))
  "Superset case"
  (assume [x T
           Hx (elem T x s)]
    (have <c> (not (elem T x (emptyset T)))
          :by ((sets/emptyset-prop T) x))
    (have <d> (and (elem T x s)
                   (not (elem T x (emptyset T))))
          :by (p/and-intro% Hx <c>)))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))

(defthm diff-empty-left
  [[T :type] [s (set T)]]
  (seteq T (diff T (emptyset T) s) (emptyset T)))

(proof diff-empty-left
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (diff T (emptyset T) s))]
    (have <a> (elem T x (emptyset T))
          :by (p/and-elim-left% Hx)))
  "Superset case"
  (assume [x T
           Hx (elem T x (emptyset T))]
    (have <b> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <c> _ :by (<b> (elem T x (diff T (emptyset T) s)))))
  (have <d> _ :by (p/and-intro% <a> <c>))
  (qed <d>))

(defthm diff-cancel
  [[T :type] [s (set T)]]
  (seteq T (diff T s s) (emptyset T)))

(proof diff-cancel
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (diff T s s))]
    (have <a1> (elem T x s) :by (p/and-elim-left% Hx))
    (have <a2> (not (elem T x s)) :by (p/and-elim-right% Hx))
    (have <b> (elem T x (emptyset T)) :by (<a2> <a1>)))
  "Superset case"
  (assume [x T
           Hx (elem T x (emptyset T))]
    (have <c> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <d> _ :by (<c> (elem T x (diff T s s)))))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))


(definition complement
  "The complement of set `s`.

Note that the definition is more self-contained
in type theory than with classical sets. The complement
is here wrt. a type `T` which is well defined,
 wherease in classical set theory one has to introduce
a somewhat unsatisfying notion of \"a universe of discourse\"."
  [[T :type] [s (set T)]]
  (lambda [x T]
    (not (elem T x s))))

(defthm comp-full-empty
  [[T :type]]
  (seteq T
         (complement T (fullset T))
         (emptyset T)))

(proof comp-full-empty
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (complement T (fullset T)))]
    (have <a> (not (elem T x (fullset T))) :by Hx)
    (have <b> p/absurd :by (<a> ((sets/fullset-intro T) x))))
  "Superset case"
  (assume [x T
           Hx (elem T x (emptyset T))]
    (have <c> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <d> _ :by (<c> (elem T x (complement T (fullset T))))))
  (have <e> _ :by (p/and-intro% <b> <d>))
  (qed <e>))

(defthm comp-empty-full
  [[T :type]]
  (seteq T
         (complement T (emptyset T))
         (fullset T)))

(proof comp-empty-full
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (complement T (emptyset T)))]
    (have <a> (elem T x (fullset T))
          :by ((sets/fullset-intro T) x)))
  "Superset case"
  (assume [x T
           Hx (elem T x (fullset T))]
    (have <b> (not (elem T x (emptyset T)))
          :by ((sets/emptyset-prop T) x)))
  (have <c> _ :by (p/and-intro% <a> <b>))
  (qed <c>))


)
