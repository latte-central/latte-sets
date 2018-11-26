(ns latte-sets.algebra
  "The boolean algebra operators for sets."

  (:refer-clojure :exclude [and or not set complement])

  (:require [latte.core :as latte
             :refer [definition defthm defaxiom defnotation
                     defimplicit forall lambda 
                     assume have pose qed proof]]
 
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-sets.core :as sets
             :refer [set elem subset seteq set-equal emptyset fullset
                     fetch-set-type]]))

(definition union-def
  "Set union.
`(union-def T s1 s2)` is the set `s1`∪`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (or (elem x s1)
        (elem x s2))))

(defimplicit union
  "Set union, `(union s1 s2)` is the set `s1`∪`s2`, cf. [[union-def]]."
  [def-env ctx [s1 s1-ty] [s2 s2-ty]]
  (let [T (fetch-set-type def-env ctx s1-ty)]
    (list #'union-def T s1 s2)))

(defthm union-idem
  [[T :type] [s (set T)]]
  (seteq (union s s) s))

(proof 'union-idem
  "We first prove that `s`∪`s`⊆`s`."
  (assume [x T
           Hx (elem x (union s s))]
    (have <a> (or (elem x s)
                  (elem x s)) :by Hx)
    (assume [Hor (elem x s)]
      (have <b> (elem x s) :by Hor))
    (have <c> (elem x s)
          :by (p/or-elim <a> (elem x s) <b> <b>)))
  "We next prove that `s`⊆ `s`∪`s`"
  (assume [x T
           Hx (elem x s)]
    (have <d> (or (elem x s)
                  (elem x s))
          :by (p/or-intro-left Hx (elem x s))))
  (qed (p/and-intro <c> <d>)))

(defthm union-empty
  [[T :type] [s (set T)]]
  (seteq (union s (emptyset T))
         s))

(proof 'union-empty
  "subset case"
  (assume [x T
           Hx (elem x (union s (emptyset T)))]
    (have <a> (or (elem x s)
                  (elem x (emptyset T))) :by Hx)
    (assume [H1 (elem x s)]
      (have <b> (elem x s) :by H1))
    (assume [H2 (elem x (emptyset T))]
      (have <c> p/absurd :by H2)
      (have <d> (elem x s) :by (<c> (elem x s))))
    (have <e> _ :by (p/or-elim <a> (elem x s) <b> <d>)))
  "superset case"
  (assume [x T
           Hx (elem x s)]
    (have <f> (or (elem x s)
                  (elem x (emptyset T)))
          :by (p/or-intro-left Hx (elem x (emptyset T)))))
  (qed (p/and-intro <e> <f>)))

(defthm union-commute
  "Set union commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq (union s1 s2)
         (union s2 s1)))

(proof 'union-commute
  (assume [x T
           H (elem x (union s1 s2))]
    (have <a1> (or (elem x s1)
                   (elem x s2)) :by H)
    (have <a2> _ :by (p/or-sym-thm (elem x s1) (elem x s2)))
    (have <a3> (or (elem x s2)
                   (elem x s1)) :by (<a2> <a1>))
    (have <a> (elem x (union s2 s1)) :by <a3>))
  (assume [x T
           H (elem x (union s2 s1))]
    (have <b> (elem x (union s1 s2))
          :by (p/or-sym H)))
  (have <c> (seteq (union s1 s2)
                   (union s2 s1))
        :by (p/and-intro <a> <b>))
  (qed <c>))

(defthm union-assoc
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (union s1 (union s2 s3))
         (union (union s1 s2) s3)))

(proof 'union-assoc
  "Subset case"
  (assume [x T
           Hx (elem x (union s1 (union s2 s3)))]
    (have <a> (or (elem x s1)
                  (elem x (union s2 s3))) :by Hx)
    (assume [H1 (elem x s1)]
      (have <b1> (or (elem x s1)
                     (elem x s2))
            :by (p/or-intro-left H1 (elem x s2)))
      (have <b> (or (or (elem x s1)
                        (elem x s2))
                    (elem x s3))
            :by (p/or-intro-left <b1> (elem x s3))))
    (assume [H2 (elem x (union s2 s3))]
      (have <c1> (or (elem x s2)
                     (elem x s3)) :by H2)
      (assume [H3 (elem x s2)]
        (have <d1> (or (elem x s1)
                       (elem x s2))
              :by (p/or-intro-right (elem x s1) H3))
        (have <d> (or (or (elem x s1)
                          (elem x s2))
                      (elem x s3))
              :by (p/or-intro-left <d1> (elem x s3))))
      (assume [H3 (elem x s3)]
        (have <e> (or (or (elem x s1)
                          (elem x s2))
                      (elem x s3))
              :by (p/or-intro-right (or (elem x s1)
                                        (elem x s2))
                                    H3)))
      (have <c> _ :by (p/or-elim <c1> (or (or (elem x s1)
                                              (elem x s2))
                                          (elem x s3))
                                  <d> <e>)))
    (have <f> (elem x (union (union s1 s2) s3))
          :by (p/or-elim <a> (or (or (elem x s1)
                                     (elem x s2))
                                 (elem x s3))
                         <b> <c>)))
  "Superset case"
  (assume [x T
           Hx (elem x (union (union s1 s2) s3))]
    (have <g> (or (elem x (union s1 s2))
                  (elem x s3)) :by Hx)
    (assume [H1 (elem x (union s1 s2))]
      (have <h1> (or (elem x s1)
                     (elem x s2)) :by H1)
      (assume [H2 (elem x s1)]
        (have <i> (or (elem x s1)
                      (or (elem x s2)
                          (elem x s3)))
              :by (p/or-intro-left H2 (or (elem x s2)
                                          (elem x s3)))))
      (assume [H3 (elem x s2)]
        (have <j1> (or (elem x s2)
                       (elem x s3))
              :by (p/or-intro-left H3 (elem x s3)))
        (have <j> (or (elem x s1)
                      (or (elem x s2)
                          (elem x s3)))
              :by (p/or-intro-right (elem x s1) <j1>)))
      (have <h> _ :by (p/or-elim <h1> (or (elem x s1)
                                          (or (elem x s2)
                                              (elem x s3)))
                                  <i> <j>)))
    (assume [H2 (elem x s3)]
      (have <k1> (or (elem x s2)
                     (elem x s3))
            :by (p/or-intro-right (elem x s2) H2))
      (have <k> (or (elem x s1)
                    (or (elem x s2)
                        (elem x s3)))
            :by (p/or-intro-right (elem x s1) <k1>)))
    (have <l> (elem x (union s1 (union s2 s3)))
          :by (p/or-elim <g> (or (elem x s1)
                                 (or (elem x s2)
                                     (elem x s3)))
                         <h> <k>)))
  (qed (p/and-intro <f> <l>)))

(defthm union-assoc-sym
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (union (union s1 s2) s3)
         (union s1 (union s2 s3))))

(proof 'union-assoc-sym
  (have <a> (seteq (union s1 (union s2 s3))
                   (union (union s1 s2) s3))
        :by (union-assoc T s1 s2 s3))
  (qed ((sets/seteq-sym (union s1 (union s2 s3))
                        (union (union s1 s2) s3))
        <a>)))

(definition inter-def
  "Set intersection.

`(inter s1 s2)` is the set `s1`∩`s2`."

  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem x s1)
         (elem x s2))))

(defimplicit inter
  "Set intersection, `(inter s1 s2)` is the set `s1`∩`s2`, cf. [[inter-def]]."
  [def-env ctx [s1 s1-ty] [s2 s2-ty]]
  (let [T (fetch-set-type def-env ctx s1-ty)]
    (list #'inter-def T s1 s2)))


(defthm inter-elim-left
  "Elimination rule for intersection (left operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem x (inter s1 s2))
       (elem x s1)))

(proof 'inter-elim-left
  (assume [H (elem x (inter s1 s2))]
    (have <a> (elem x s1) :by (p/and-elim-left H)))
  (qed <a>))

(defthm inter-elim-right
  "Elimination rule for intersection (right operand)."
  [[T :type] [s1 (set T)] [s2 (set T)] [x T]]
  (==> (elem x (inter s1 s2))
       (elem x s2)))

(proof 'inter-elim-right
  (assume [H (elem x (inter s1 s2))]
    (have <a> (elem x s2) :by (p/and-elim-right H)))
    (qed <a>))

(defthm inter-idem
  [[T :type] [s (set T)]]
  (seteq (inter s s) s))

(proof 'inter-idem
  "Subset case"
  (assume [x T
           Hx (elem x (inter s s))]
    (have <a> (elem x s) :by (p/and-elim-left Hx)))
  "Superset case"
  (assume [x T
           Hx (elem x s)]
    (have <b> (elem x (inter s s))
          :by (p/and-intro Hx Hx)))
  (qed (p/and-intro <a> <b>)))

(defthm inter-empty
  [[T :type] [s (set T)]]
  (seteq (inter s (emptyset T))
         (emptyset T)))

(proof 'inter-empty
  "Subset case."
  (assume [x T
           Hx (elem x (inter s (emptyset T)))]
    (have <a> (elem x (emptyset T))
          :by (p/and-elim-right Hx)))
  "Superset case"
  (assume [x T
           Hx (elem x (emptyset T))]
    (have <b> p/absurd :by Hx)
    (have <c> _ :by (<b> (elem x (inter s (emptyset T))))))
  (qed (p/and-intro <a> <c>)))

(defthm inter-commute
  "Set intersection commutes."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq (inter s1 s2)
         (inter s2 s1)))

(proof 'inter-commute
  (assume [x T
           H (elem x (inter s1 s2))]
    (have <a> (elem x (inter s2 s1))
          :by (p/and-sym H)))
  (assume [x T
           H (elem x (inter s2 s1))]
    (have <b> (elem x (inter s1 s2))
          :by (p/and-sym H)))
  (have <c> (seteq (inter s1 s2)
                   (inter s2 s1))
        :by (p/and-intro <a> <b>))
  (qed <c>))

(defthm inter-assoc
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (inter s1 (inter s2 s3))
         (inter (inter s1 s2) s3)))

(proof 'inter-assoc
  "Subset case"
  (assume [x T
           Hx (elem x (inter s1 (inter s2 s3)))]
    (have <a1> (and (elem x s1)
                    (and (elem x s2)
                         (elem x s3))) :by Hx)
    (have <a2> (elem x s1) :by (p/and-elim-left <a1>))
    (have <a3> (elem x s2) :by (p/and-elim-left (p/and-elim-right <a1>)))
    (have <a4> (elem x s3) :by (p/and-elim-right (p/and-elim-right <a1>)))
    (have <a> _ :by (p/and-intro (p/and-intro <a2> <a3>) <a4>)))
  "Superset case"
  (assume [x T
           Hx (elem x (inter (inter s1 s2) s3))]
    (have <b1> (and (and (elem x s1)
                         (elem x s2))
                    (elem x s3)) :by Hx)
    (have <b2> (elem x s3) :by (p/and-elim-right <b1>))
    (have <b3> (elem x s1) :by (p/and-elim-left (p/and-elim-left <b1>)))
    (have <b4> (elem x s2) :by (p/and-elim-right (p/and-elim-left <b1>)))
    (have <b> _ :by (p/and-intro <b3> (p/and-intro <b4> <b2>))))
  (qed (p/and-intro <a> <b>)))

(defthm inter-assoc-sym
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (inter (inter s1 s2) s3)
         (inter s1 (inter s2 s3))))

(proof 'inter-assoc-sym
  (have <a> (seteq (inter s1 (inter s2 s3))
                   (inter (inter s1 s2) s3))
        :by (inter-assoc T s1 s2 s3))
  (qed ((sets/seteq-sym (inter s1 (inter s2 s3))
                        (inter (inter s1 s2) s3))
        <a>)))

(defthm dist-union-inter
  "Distributivity of union over intersection."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (union s1 (inter s2 s3))
         (inter (union s1 s2) (union s1 s3))))

(proof 'dist-union-inter
  "Subset case"
  (assume [x T
           Hx (elem x (union s1 (inter s2 s3)))]
    (have <a> (or (elem x s1)
                  (and (elem x s2)
                       (elem x s3))) :by Hx)
    (assume [H1 (elem x s1)]
      (have <b1> (or (elem x s1)
                     (elem x s2))
            :by (p/or-intro-left H1 (elem x s2)))
      (have <b2> (or (elem x s1)
                     (elem x s3))
            :by (p/or-intro-left H1 (elem x s3)))
      (have <b> _ :by (p/and-intro <b1> <b2>)))
    (assume [H2 (and (elem x s2)
                     (elem x s3))]
      (have <c1> (or (elem x s1)
                     (elem x s2))
            :by (p/or-intro-right (elem x s1)
                                  (p/and-elim-left H2)))
      (have <c2> (or (elem x s1)
                     (elem x s3))
            :by (p/or-intro-right (elem x s1)
                                  (p/and-elim-right H2)))
      (have <c> _ :by (p/and-intro <c1> <c2>)))
    (have <d> (elem x (inter (union s1 s2) (union s1 s3)))
          :by (p/or-elim <a>
                         (elem x (inter (union s1 s2) (union s1 s3)))
                         <b> <c>)))
  "Superset case"
  (assume [x T
           Hx (elem x (inter (union s1 s2) (union s1 s3)))]
    (have <e> (or (elem x s1)
                  (elem x s2))
          :by (p/and-elim-left Hx))
    (have <f> (or (elem x s1)
                  (elem x s3))
          :by (p/and-elim-right Hx))
    (assume [H1 (elem x s1)]
      (have <g> (or (elem x s1)
                    (and (elem x s2)
                         (elem x s3)))
            :by (p/or-intro-left H1 (and (elem x s2)
                                         (elem x s3)))))  
    (assume [H2 (elem x s2)]
      (assume [H3 (elem x s1)]
        (have <h> (or (elem x s1)
                      (and (elem x s2)
                           (elem x s3)))
              :by (p/or-intro-left H3 (and (elem x s2)
                                           (elem x s3)))))
       (assume [H4 (elem x s3)]
         (have <i1> _ :by (p/and-intro H2 H4))
         (have <i> (or (elem x s1)
                       (and (elem x s2)
                            (elem x s3)))
               :by (p/or-intro-right (elem x s1)
                                     <i1>)))
       (have <j> _ :by (p/or-elim <f> (or (elem x s1)
                                          (and (elem x s2)
                                               (elem x s3)))
                                  <h> <i>)))
     (have <k> (elem x (union s1 (inter s2 s3)))
           :by (p/or-elim <e> (or (elem x s1)
                                  (and (elem x s2)
                                       (elem x s3)))
                          <g> <j>)))
  (qed (p/and-intro <d> <k>)))


(defthm dist-union-inter-sym
  "Symmetric case of [[dist-union-inter]]."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (inter (union s1 s2) (union s1 s3))
         (union s1 (inter s2 s3))))

(proof 'dist-union-inter-sym
  (have <a> (seteq (union s1 (inter s2 s3))
                   (inter (union s1 s2) (union s1 s3)))
        :by (dist-union-inter T s1 s2 s3))
  (qed ((sets/seteq-sym (union s1 (inter s2 s3))
                        (inter (union s1 s2) (union s1 s3))) <a>)))

(defthm dist-inter-union
  "Distributivity of intersection over union."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq (inter s1 (union s2 s3))
         (union (inter s1 s2) (inter s1 s3))))

(proof 'dist-inter-union
  "Subset case"
  (assume [x T
           Hx (elem x (inter s1 (union s2 s3)))]
    (have <a> (elem x s1) :by (p/and-elim-left Hx))
    (have <b> (or (elem x s2)
                  (elem x s3)) :by (p/and-elim-right Hx))
    (assume [H1 (elem x s2)]
      (have <c1> (and (elem x s1) (elem x s2))
            :by (p/and-intro <a> H1))
      (have <c> (or (and (elem x s1) (elem x s2))
                    (and (elem x s1) (elem x s3)))
            :by (p/or-intro-left <c1> (and (elem x s1) (elem x s3)))))
    (assume [H2 (elem x s3)]
      (have <d1> (and (elem x s1) (elem x s3))
            :by (p/and-intro <a> H2))
      (have <d> (or (and (elem x s1) (elem x s2))
                    (and (elem x s1) (elem x s3)))
            :by (p/or-intro-right (and (elem x s1) (elem x s2))
                                  <d1>)))
    (have <e> (elem x (union (inter s1 s2) (inter s1 s3)))
          :by (p/or-elim <b> (or (and (elem x s1) (elem x s2))
                                 (and (elem x s1) (elem x s3)))
                         <c> <d>)))
  "Superset case"
  (assume [x T
           Hx (elem x (union (inter s1 s2) (inter s1 s3)))]
    (have <f> (or (and (elem x s1) (elem x s2))
                  (and (elem x s1) (elem x s3))) :by Hx)
    (assume [H1 (and (elem x s1) (elem x s2))]
      (have <g1> (elem x s1) :by (p/and-elim-left H1))
      (have <g2> (or (elem x s2)
                     (elem x s3))
            :by (p/or-intro-left (p/and-elim-right H1)
                                 (elem x s3)))
      (have <g> (and (elem x s1)
                     (or (elem x s2)
                         (elem x s3)))
            :by (p/and-intro <g1> <g2>)))
    (assume [H2 (and (elem x s1) (elem x s3))]
      (have <h1> (elem x s1) :by (p/and-elim-left H2))
      (have <h2> (or (elem x s2)
                     (elem x s3))
            :by (p/or-intro-right (elem x s2)
                                  (p/and-elim-right H2)))
      (have <h> (and (elem x s1)
                     (or (elem x s2)
                         (elem x s3)))
            :by (p/and-intro <h1> <h2>)))
    (have <i> (elem x (inter s1 (union s2 s3)))
          :by (p/or-elim <f> (and (elem x s1)
                                  (or (elem x s2)
                                      (elem x s3)))
                         <g> <h>)))
  (qed (p/and-intro <e> <i>)))

(defthm dist-inter-union-sym
  "Symmetric case of [[dist-inter-union]]."
  [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
  (seteq
         (union (inter s1 s2) (inter s1 s3))
         (inter s1 (union s2 s3))))

(proof 'dist-inter-union-sym
  (have <a> (seteq (inter s1 (union s2 s3))
                   (union (inter s1 s2) (inter s1 s3)))
        :by (dist-inter-union T s1 s2 s3))
  (qed ((sets/seteq-sym
         (inter s1 (union s2 s3))
         (union (inter s1 s2) (inter s1 s3))) <a>)))


(definition diff-def
  "Set difference

`(difference T s1 s2)` is the set `s1`∖`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (and (elem x s1)
         (not (elem x s2)))))

(defimplicit diff
  "Set difference, `(diff s1 s2)` is the set `s1`∖`s2`, cf. [[diff-def]]."
  [def-env ctx [s1 s1-ty] [s2 s2-ty]]
  (let [T (fetch-set-type def-env ctx s1-ty)]
    (list #'diff-def T s1 s2)))


(defthm diff-empty-right
  [[T :type] [s (set T)]]
  (seteq (diff s (emptyset T)) s))

(proof 'diff-empty-right
  "Subset case"
  (assume [x T
           Hx (elem x (diff s (emptyset T)))]
    (have <a> (and (elem x s)
                   (not (elem x (emptyset T)))) :by Hx)
    (have <b> (elem x s) :by (p/and-elim-left <a>)))
  "Superset case"
  (assume [x T
           Hx (elem x s)]
    (have <c> (not (elem x (emptyset T)))
          :by ((sets/emptyset-prop T) x))
    (have <d> (and (elem x s)
                   (not (elem x (emptyset T))))
          :by (p/and-intro Hx <c>)))
  (qed (p/and-intro <b> <d>)))

(defthm diff-empty-left
  [[T :type] [s (set T)]]
  (seteq (diff (emptyset T) s) (emptyset T)))

(proof 'diff-empty-left
  "Subset case"
  (assume [x T
           Hx (elem x (diff (emptyset T) s))]
    (have <a> (elem x (emptyset T))
          :by (p/and-elim-left Hx)))
  "Superset case"
  (assume [x T
           Hx (elem x (emptyset T))]
    (have <b> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <c> _ :by (<b> (elem x (diff (emptyset T) s)))))
  (qed (p/and-intro <a> <c>)))

(defthm diff-cancel
  [[T :type] [s (set T)]]
  (seteq (diff s s) (emptyset T)))

(proof 'diff-cancel
  "Subset case"
  (assume [x T
           Hx (elem x (diff s s))]
    (have <a1> (elem x s) :by (p/and-elim-left Hx))
    (have <a2> (not (elem x s)) :by (p/and-elim-right Hx))
    (have <b> (elem x (emptyset T)) :by (<a2> <a1>)))
  "Superset case"
  (assume [x T
           Hx (elem x (emptyset T))]
    (have <c> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <d> _ :by (<c> (elem x (diff s s)))))
  (qed (p/and-intro <b> <d>)))

(definition symdiff-def
  "Symmetric difference, often denoted by `s1`∆`s2`."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (lambda [x T]
    (or (and (elem x s1) (not (elem x s2)))
        (and (elem x s2) (not (elem x s1))))))

(defimplicit symdiff
  "Symmetric difference, `(symdiff s1 s2)` is the set `s1`∆`s2`, cf. [[symdiff-def]]."
  [def-env ctx [s1 s1-ty] [s2 s2-ty]]
  (let [T (fetch-set-type def-env ctx s1-ty)]
    (list #'symdiff-def T s1 s2)))

(defthm symdiff-alt
  "An alternative caracterisation of the symmetric difference."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (seteq (symdiff s1 s2)
         (union (diff s1 s2)
                (diff s2 s1))))

(proof 'symdiff-alt
  "Subset case"
  (assume [x T
           Hx (elem x (symdiff s1 s2))]
    (have <a> (or (and (elem x s1) (not (elem x s2)))
                  (and (elem x s2) (not (elem x s1))))
          :by Hx)
    (have <b> (elem x (union
                               (diff s1 s2)
                               (diff s2 s1))) :by <a>))
  "Superset case."
  (assume [x T
           Hx (elem x (union
                               (diff s1 s2)
                               (diff s2 s1)))]
    (have <c> (or (elem x (diff s1 s2))
                  (elem x (diff s2 s1))) :by Hx)
    (have <d> (elem x (symdiff s1 s2)) :by <c>))
  (qed (p/and-intro <b> <d>)))


(definition complement-def
  "The complement of set `s`.

Note that the definition is more self-contained
in type theory than with classical sets. The complement
is here wrt. a type `T` which is well defined,
 wherease in classical set theory one has to introduce
a somewhat unsatisfying notion of \"a universe of discourse\"."
  [[T :type] [s (set T)]]
  (lambda [x T]
          (not (elem x s))))

(defimplicit complement
  "Set complement. Given a set `s` of type `(set T)`, then `(complement s)` 
 with all the inhabitants of `T` that are not member of set `s`, cf. [[complement-def]]."
  [def-env ctx [s s-ty]]
  (let [T (fetch-set-type def-env ctx s-ty)]
    (list #'complement-def T s)))

(defthm comp-full-empty
  [[T :type]]
  (seteq (complement (fullset T))
         (emptyset T)))

(proof 'comp-full-empty
  "Subset case"
  (assume [x T
           Hx (elem x (complement (fullset T)))]
    (have <a> (not (elem x (fullset T))) :by Hx)
    (have <b> p/absurd :by (<a> ((sets/fullset-intro T) x))))
  "Superset case"
  (assume [x T
           Hx (elem x (emptyset T))]
    (have <c> p/absurd :by (((sets/emptyset-prop T) x) Hx))
    (have <d> _ :by (<c> (elem x (complement (fullset T))))))
  (qed (p/and-intro <b> <d>)))

(defthm comp-empty-full
  [[T :type]]
  (seteq (complement (emptyset T))
         (fullset T)))

(proof 'comp-empty-full
  "Subset case"
  (assume [x T
           Hx (elem x (complement (emptyset T)))]
    (have <a> (elem x (fullset T))
          :by ((sets/fullset-intro T) x)))
  "Superset case"
  (assume [x T
           Hx (elem x (fullset T))]
    (have <b> (not (elem x (emptyset T)))
          :by ((sets/emptyset-prop T) x)))
  (qed (p/and-intro <a> <b>)))





