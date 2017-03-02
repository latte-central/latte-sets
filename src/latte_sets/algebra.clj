(ns latte-sets.algebra
  "The boolean algebra operators for sets."

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte
             :refer [definition defthm defaxiom defnotation
                     forall lambda ==>
                     assume have pose proof lambda forall]]
            
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as sets
             :refer [set elem subset seteq set-equal emptyset]]))

(definition union
  "Set union.
`(union T s1 s2)` is the set `s1`∪`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (or (elem T x s1)
        (elem T x s2))))

(defthm union-idem
  [[T :type] [s (set T)]]
  (seteq T (union T s s) s))

(proof union-idem
    :script
  "We first prove that `s`∪`s`⊆`s`."
  (assume [x T
           Hx (elem T x (union T s s))]
    (have <a> (or (elem T x s)
                  (elem T x s)) :by Hx)
    (assume [Hor (elem T x s)]
      (have <b> (elem T x s) :by Hor))
    (have <c> (elem T x s)
          :by (p/or-elim% <a> (elem T x s) <b> <b>)))
  "We next prove that `s`⊆ `s`∪`s`"
  (assume [x T
           Hx (elem T x s)]
    (have <d> (or (elem T x s)
                  (elem T x s))
          :by (p/or-intro-left% Hx (elem T x s))))
  (have <e> _ :by (p/and-intro% <c> <d>))
  (qed <e>))

(defthm union-empty
  [[T :type] [s (set T)]]
  (seteq T
         (union T s (emptyset T))
         s))

(proof union-empty
    :script
  "subset case"
  (assume [x T
           Hx (elem T x (union T s (emptyset T)))]
    (have <a> (or (elem T x s)
                  (elem T x (emptyset T))) :by Hx)
    (assume [H1 (elem T x s)]
      (have <b> (elem T x s) :by H1))
    (assume [H2 (elem T x (emptyset T))]
      (have <c> p/absurd :by H2)
      (have <d> (elem T x s) :by (<c> (elem T x s))))
    (have <e> _ :by (p/or-elim% <a> (elem T x s) <b> <d>)))
  "superset case"
  (assume [x T
           Hx (elem T x s)]
    (have <f> (or (elem T x s)
                  (elem T x (emptyset T)))
          :by (p/or-intro-left% Hx (elem T x (emptyset T)))))
  (have <g> _ :by (p/and-intro% <e> <f>))
  (qed <g>))

(defthm union-commute
  "Set union commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq T
         (union T s1 s2)
         (union T s2 s1)))

(proof union-commute :script
  (assume [x T
           H (elem T x (union T s1 s2))]
    (have a1 (or (elem T x s1)
                 (elem T x s2)) :by H)
    (have a2 _ :by (p/or-sym (elem T x s1) (elem T x s2)))
    (have a3 (or (elem T x s2)
                 (elem T x s1)) :by (a2 a1))
    (have a (elem T x (union T s2 s1)) :by a3))
  (assume [x T
           H (elem T x (union T s2 s1))]
    (have b (elem T x (union T s1 s2))
          :by ((p/or-sym (elem T x s2) (elem T x s1)) H)))
  (have c (seteq T
                 (union T s1 s2)
                 (union T s2 s1))
        :by (p/and-intro% a b))
  (qed c))

(defthm union-assoc
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (union T s1 (union T s2 s3))
         (union T (union T s1 s2) s3)))

(proof union-assoc
    :script
  "Subset case"
  (assume [x T
           Hx (elem T x (union T s1 (union T s2 s3)))]
    (have <a> (or (elem T x s1)
                  (elem T x (union T s2 s3))) :by Hx)
    (assume [H1 (elem T x s1)]
      (have <b1> (or (elem T x s1)
                     (elem T x s2))
            :by (p/or-intro-left% H1 (elem T x s2)))
      (have <b> (or (or (elem T x s1)
                        (elem T x s2))
                    (elem T x s3))
            :by (p/or-intro-left% <b1> (elem T x s3))))
    (assume [H2 (elem T x (union T s2 s3))]
      (have <c1> (or (elem T x s2)
                     (elem T x s3)) :by H2)
      (assume [H3 (elem T x s2)]
        (have <d1> (or (elem T x s1)
                       (elem T x s2))
              :by (p/or-intro-right% (elem T x s1) H3))
        (have <d> (or (or (elem T x s1)
                          (elem T x s2))
                      (elem T x s3))
              :by (p/or-intro-left% <d1> (elem T x s3))))
      (assume [H3 (elem T x s3)]
        (have <e> (or (or (elem T x s1)
                          (elem T x s2))
                      (elem T x s3))
              :by (p/or-intro-right% (or (elem T x s1)
                                         (elem T x s2))
                                     H3)))
      (have <c> _ :by (p/or-elim% <c1> (or (or (elem T x s1)
                                               (elem T x s2))
                                           (elem T x s3))
                                  <d> <e>)))
    (have <f> (elem T x (union T (union T s1 s2) s3))
          :by (p/or-elim% <a> (or (or (elem T x s1)
                                      (elem T x s2))
                                  (elem T x s3))
                          <b> <c>)))
  "Superset case"
  (assume [x T
           Hx (elem T x (union T (union T s1 s2) s3))]
    (have <g> (or (elem T x (union T s1 s2))
                  (elem T x s3)) :by Hx)
    (assume [H1 (elem T x (union T s1 s2))]
      (have <h1> (or (elem T x s1)
                     (elem T x s2)) :by H1)
      (assume [H2 (elem T x s1)]
        (have <i> (or (elem T x s1)
                      (or (elem T x s2)
                          (elem T x s3)))
              :by (p/or-intro-left% H2 (or (elem T x s2)
                                           (elem T x s3)))))
      (assume [H3 (elem T x s2)]
        (have <j1> (or (elem T x s2)
                       (elem T x s3))
              :by (p/or-intro-left% H3 (elem T x s3)))
        (have <j> (or (elem T x s1)
                      (or (elem T x s2)
                          (elem T x s3)))
              :by (p/or-intro-right% (elem T x s1) <j1>)))
      (have <h> _ :by (p/or-elim% <h1> (or (elem T x s1)
                                           (or (elem T x s2)
                                               (elem T x s3)))
                                  <i> <j>)))
    (assume [H2 (elem T x s3)]
      (have <j1> (or (elem T x s2)
                     (elem T x s3))
            :by (p/or-intro-right% (elem T x s2) H2))
      (have <j> (or (elem T x s1)
                    (or (elem T x s2)
                        (elem T x s3)))
            :by (p/or-intro-right% (elem T x s1) <j1>)))
    (have <k> (elem T x (union T s1 (union T s2 s3)))
          :by (p/or-elim% <g> (or (elem T x s1)
                                  (or (elem T x s2)
                                      (elem T x s3)))
                          <h> <j>)))
  (have <l> _ :by (p/and-intro% <f> <k>))
  (qed <l>))

(defthm union-assoc-sym
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq T
         (union T (union T s1 s2) s3)
         (union T s1 (union T s2 s3))))

(proof union-assoc-sym
    :script
  (have <a> (seteq T
                   (union T s1 (union T s2 s3))
                   (union T (union T s1 s2) s3))
        :by (union-assoc T s1 s2 s3))
  (have <b> _ :by ((sets/seteq-sym T
                                   (union T s1 (union T s2 s3))
                                   (union T (union T s1 s2) s3))
                   <a>))
  (qed <b>))

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


(definition difference
  "Set difference

`(difference T s1 s2)` is the set `s1`∖`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem T x s1)
         (not (elem T x s2)))))



