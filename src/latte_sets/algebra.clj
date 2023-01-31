(ns latte-sets.algebra
  "The boolean algebra operators for sets."

  (:refer-clojure :exclude [and or not set complement])

  (:require [latte.core :as latte
             :refer [definition defthm defaxiom defnotation
                     defimplicit forall lambda 
                     assume have pose qed proof try-proof]]
 
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.classic :as classic]

            [latte-sets.set :as sets
             :refer [set set-of elem subset seteq set-equal emptyset fullset
                     fetch-set-type]]))

(definition union
  "Set union, `(union s1 s2)` is the set `s1`∪`s2`."
  [?T :type, [s1 s2 (set T)]]
  (lambda [x T]
    (or (elem x s1)
        (elem x s2))))

(defthm union-idem
  [?T :type, s (set T)]
  (seteq (union s s) s))

(proof 'union-idem-thm
  "We first prove that `s`∪`s`⊆`s`."
  (assume [x T
           Hx (elem x (union s s))]
    (have <a> (or (elem x s)
                  (elem x s)) :by Hx)
    (assume [Hor (elem x s)]
      (have <b> (elem x s) :by Hor))
    (have <c> (elem x s)
          :by (p/or-elim <a> <b> <b>)))
  "We next prove that `s`⊆ `s`∪`s`"
  (assume [x T
           Hx (elem x s)]
    (have <d> (or (elem x s)
                  (elem x s))
          :by (p/or-intro-left Hx (elem x s))))
  (qed (p/and-intro <c> <d>)))

(defthm union-not-left
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x (union s1 s2)))
       (not (elem x s1))))

(proof 'union-not-left-thm
  (assume [H _]
    "By contradiction"
    (assume [Hcontra (elem x s1)]
      (have <a1> (elem x (union s1 s2))
            :by (p/or-intro-left Hcontra (elem x s2)))
      (have <a> p/absurd :by (H <a1>))))
  (qed <a>))

(defthm union-not-right
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x (union s1 s2)))
       (not (elem x s2))))

(proof 'union-not-right-thm
  (assume [H _]
    "By contradiction"
    (assume [Hcontra (elem x s2)]
      (have <a1> (elem x (union s1 s2))
            :by (p/or-intro-right (elem x s1) Hcontra))
      (have <a> p/absurd :by (H <a1>))))
  (qed <a>))
  
(defthm union-empty
  [?T :type, s (set T)]
  (seteq (union s (emptyset T))
         s))

(proof 'union-empty-thm
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
    (have <e> _ :by (p/or-elim <a> <b> <d>)))
  "superset case"
  (assume [x T
           Hx (elem x s)]
    (have <f> (or (elem x s)
                  (elem x (emptyset T)))
          :by (p/or-intro-left Hx (elem x (emptyset T)))))
  (qed (p/and-intro <e> <f>)))

(defthm union-commute
  "Set union commutes."
  [?T :type, [s1 s2 (set T)]]
  (seteq (union s1 s2)
         (union s2 s1)))

(proof 'union-commute-thm
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
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (union s1 (union s2 s3))
         (union (union s1 s2) s3)))

(proof 'union-assoc-thm
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
      (have <c> (or (or (elem x s1)
                        (elem x s2))
                    (elem x s3)) :by (p/or-elim <c1> <d> <e>)))
    (have <f> (elem x (union (union s1 s2) s3))
          :by (p/or-elim <a> <b> <c>)))
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
      (have <h> (or (elem x s1)
                    (or (elem x s2)
                        (elem x s3))) :by (p/or-elim <h1> <i> <j>)))
    (assume [H2 (elem x s3)]
      (have <k1> (or (elem x s2)
                     (elem x s3))
            :by (p/or-intro-right (elem x s2) H2))
      (have <k> (or (elem x s1)
                    (or (elem x s2)
                        (elem x s3)))
            :by (p/or-intro-right (elem x s1) <k1>)))
    (have <l> (elem x (union s1 (union s2 s3)))
          :by (p/or-elim <g> <h> <k>)))
  (qed (p/and-intro <f> <l>)))

(defthm union-assoc-sym
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (union (union s1 s2) s3)
         (union s1 (union s2 s3))))

(proof 'union-assoc-sym-thm
  (have <a> (seteq (union s1 (union s2 s3))
                   (union (union s1 s2) s3))
        :by (union-assoc s1 s2 s3))
  (qed ((sets/seteq-sym (union s1 (union s2 s3))
                        (union (union s1 s2) s3))
        <a>)))

(definition inter
  "Set intersection, i.e. the set `s1`∩`s2`."
  [?T :type, [s1 s2 (set T)]]
  (lambda [x T]
    (and (elem x s1)
         (elem x s2))))

(defthm inter-elim-left
  "Elimination rule for intersection (left operand)."
  [?T :type, [s1 s2 (set T)], x T]
  (==> (elem x (inter s1 s2))
       (elem x s1)))

(proof 'inter-elim-left-thm
  (assume [H (elem x (inter s1 s2))]
    (have <a> (elem x s1) :by (p/and-elim-left H)))
  (qed <a>))

(defthm inter-elim-right
  "Elimination rule for intersection (right operand)."
  [?T :type, [s1 s2 (set T)], x T]
  (==> (elem x (inter s1 s2))
       (elem x s2)))

(proof 'inter-elim-right-thm
  (assume [H (elem x (inter s1 s2))]
    (have <a> (elem x s2) :by (p/and-elim-right H)))
    (qed <a>))

(defthm inter-not-left
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x s1))
       (not (elem x (inter s1 s2)))))

(proof 'inter-not-left-thm
  (assume [Hx (not (elem x s1))]
    (assume [Hcontra (elem x (inter s1 s2))]
      (have <a> (elem x s1) :by (p/and-elim-left Hcontra))
      (have <b> p/absurd :by (Hx <a>))))
  (qed <b>))

(defthm inter-not-right
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x s2))
       (not (elem x (inter s1 s2)))))

(proof 'inter-not-right-thm
  (assume [Hx (not (elem x s2))]
    (assume [Hcontra (elem x (inter s1 s2))]
      (have <a> (elem x s2) :by (p/and-elim-right Hcontra))
      (have <b> p/absurd :by (Hx <a>))))
  (qed <b>))

(defthm inter-not-inter-left
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x (inter s1 s2)))
       (elem x s1)
       (not (elem x s2))))

(proof 'inter-not-inter-left-thm
  (assume [Hinter (not (elem x (inter s1 s2)))
           Hs1 (elem x s1)]
    "We proceed by contradiction"
    (assume [Hs2 (elem x s2)]
      (have <a> p/absurd :by (Hinter (p/and-intro Hs1 Hs2)))))
  (qed <a>))

(defthm inter-not-inter-right
  [[?T :type] [s1 s2 (set T)] [x T]]
  (==> (not (elem x (inter s1 s2)))
       (elem x s2)
       (not (elem x s1))))

(proof 'inter-not-inter-right-thm
  (assume [Hinter (not (elem x (inter s1 s2)))
           Hs2 (elem x s2)]
    "We proceed by contradiction"
    (assume [Hs1 (elem x s1)]
      (have <a> p/absurd :by (Hinter (p/and-intro Hs1 Hs2)))))
  (qed <a>))

(defthm inter-idem
  [?T :type, s (set T)]
  (seteq (inter s s) s))

(proof 'inter-idem-thm
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
  [?T :type, s (set T)]
  (seteq (inter s (emptyset T))
         (emptyset T)))

(proof 'inter-empty-thm
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
  [?T :type, [s1 s2 (set T)]]
  (seteq (inter s1 s2)
         (inter s2 s1)))

(proof 'inter-commute-thm
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
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (inter s1 (inter s2 s3))
         (inter (inter s1 s2) s3)))

(proof 'inter-assoc-thm
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
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (inter (inter s1 s2) s3)
         (inter s1 (inter s2 s3))))

(proof 'inter-assoc-sym-thm
  (have <a> (seteq (inter s1 (inter s2 s3))
                   (inter (inter s1 s2) s3))
        :by (inter-assoc s1 s2 s3))
  (qed ((sets/seteq-sym (inter s1 (inter s2 s3))
                        (inter (inter s1 s2) s3))
        <a>)))

(definition disjoint
  [?T :type, s1 (set T), s2 (set T)]
  (set-equal (inter s1 s2) (emptyset T)))

(defthm disjoint-eq
  [?T :type, s1 (set T), s2 (set T)]
  (==> (disjoint s1 s2)
       (seteq (inter s1 s2) (emptyset T))))

(proof 'disjoint-eq-thm
  (assume [Hd (disjoint s1 s2)]
    (have <a> _ :by ((sets/set-equal-implies-seteq (inter s1 s2) (emptyset T)) Hd)))
  (qed <a>))

(defthm disjoint-elem-left
  [[?T :type] [s1 s2 (set T)]]
  (forall [x T]
    (==> (disjoint s1 s2)
         (elem x s1)
         (not (elem x s2)))))

(proof 'disjoint-elem-left-thm
  (assume [x T
           Hdis (disjoint s1 s2)
           Hx (elem x s1)]
    (assume [Hneg (elem x s2)]
      (have <a> (elem x (inter s1 s2)) :by (p/and-intro Hx Hneg))
      (have <b> (elem x (emptyset T)) 
            :by ((sets/set-equal-subst-prop (lambda [$ (set T)] (elem x $)) (inter s1 s2) (emptyset T))
                 Hdis <a>))
      (have <c> p/absurd :by (((sets/emptyset-prop T) x) <b>))))
  (qed <c>))

(defthm disjoint-elem-right
  [[?T :type] [s1 s2 (set T)]]
  (forall [x T]
    (==> (disjoint s1 s2)
         (elem x s2)
         (not (elem x s1)))))

(proof 'disjoint-elem-right-thm
  (assume [x T
           Hdis (disjoint s1 s2)
           Hx (elem x s2)]
    (assume [Hneg (elem x s1)]
      (have <a> (elem x (inter s1 s2)) :by (p/and-intro Hneg Hx))
      (have <b> (elem x (emptyset T)) 
            :by ((sets/set-equal-subst-prop (lambda [$ (set T)] (elem x $)) (inter s1 s2) (emptyset T))
                 Hdis <a>))
      (have <c> p/absurd :by (((sets/emptyset-prop T) x) <b>))))
  (qed <c>))

(defthm disjoint-complement
  [[?T :type] [s1 s2 (set T)]]
  (==> (not (disjoint s1 s2))
       (exists [x T]
         (and (elem x s1)
              (elem x s2)))))

(proof 'disjoint-complement-thm
  (pose P := (lambda [x T] (and (elem x s1) (elem x s2))))
  (assume [Hdis (not (disjoint s1 s2))]
    (assume [Hcontra (not (exists [x T] (P x)))]
      (have <a> (forall [x T] (not (P x)))
            :by ((q/not-ex-elim P) Hcontra))
      (have <b> (seteq (inter s1 s2) (emptyset T))
            :by ((sets/emptyset-seteq-intro (inter s1 s2)) <a>))
      (have <c> (set-equal (inter s1 s2) (emptyset T))
            :by ((sets/seteq-implies-set-equal (inter s1 s2) (emptyset T)) <b>))
      (have <d> p/absurd :by (Hdis <c>)))
    "Remark : we use a classical principle (double negation)"
    (have <e> _ :by ((classic/not-not-impl (exists [x T] (P x))) <d>)))
  (qed <e>))

(defthm dist-union-inter
  "Distributivity of union over intersection."
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (union s1 (inter s2 s3))
         (inter (union s1 s2) (union s1 s3))))

(proof 'dist-union-inter-thm
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
          :by (p/or-elim <a> <b> <c>)))
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
       (have <j> _ :by (p/or-elim <f> <h> <i>)))
     (have <k> (elem x (union s1 (inter s2 s3)))
           :by (p/or-elim <e> <g> <j>)))
  (qed (p/and-intro <d> <k>)))

(defthm dist-union-inter-sym
  "Symmetric case of [[dist-union-inter]]."
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (inter (union s1 s2) (union s1 s3))
         (union s1 (inter s2 s3))))

(proof 'dist-union-inter-sym-thm
  (have <a> (seteq (union s1 (inter s2 s3))
                   (inter (union s1 s2) (union s1 s3)))
        :by (dist-union-inter s1 s2 s3))
  (qed ((sets/seteq-sym (union s1 (inter s2 s3))
                        (inter (union s1 s2) (union s1 s3))) <a>)))

(defthm dist-inter-union
  "Distributivity of intersection over union."
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq (inter s1 (union s2 s3))
         (union (inter s1 s2) (inter s1 s3))))

(proof 'dist-inter-union-thm
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
          :by (p/or-elim <b> <c> <d>)))
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
          :by (p/or-elim <f> <g> <h>)))
  (qed (p/and-intro <e> <i>)))

(defthm dist-inter-union-sym
  "Symmetric case of [[dist-inter-union]]."
  [?T :type, [s1 s2 s3 (set T)]]
  (seteq
         (union (inter s1 s2) (inter s1 s3))
         (inter s1 (union s2 s3))))

(proof 'dist-inter-union-sym-thm
  (have <a> (seteq (inter s1 (union s2 s3))
                   (union (inter s1 s2) (inter s1 s3)))
        :by (dist-inter-union s1 s2 s3))
  (qed ((sets/seteq-sym
         (inter s1 (union s2 s3))
         (union (inter s1 s2) (inter s1 s3))) <a>)))

(definition diff
  "Set difference

`(difference T s1 s2)` is the set `s1`∖`s2`."
  [?T :type, [s1 s2 (set T)]]
  (lambda [x T]
    (and (elem x s1)
         (not (elem x s2)))))

(defthm diff-subset
  [[?T :type] [s1 s2 (set T)]]
  (subset (diff s1 s2) s1))

(proof 'diff-subset-thm
  (assume [x T
           Hx (elem x (diff s1 s2))]
    "We want to prove that `(elem x s1)`"
    (have <a> (elem x s1) :by (p/and-elim-left Hx)))
  (qed <a>))

(defthm diff-inter
  [[?T :type] [s1 s2 s3 (set T)]]
  (seteq (diff s3 (inter s1 s2))
         (union (diff s3 s1) (diff s3 s2))))

(proof 'diff-inter-thm
  "Subset case"
  (assume [x T
           Hx (elem x (diff s3 (inter s1 s2)))]
    (have <Hx1> (elem x s3) :by (p/and-elim-left Hx))
    (have <Hx2> (not (elem x (inter s1 s2))) :by (p/and-elim-right Hx))
    "The proof is classical"
    (have <a1> (or (elem x s1) (not (elem x s1)))
          :by (classic/excluded-middle-ax (elem x s1)))
    (assume [Ha1 (elem x s1)]
      (have <b1> (not (elem x s2))
            :by ((inter-not-inter-left s1 s2 x) <Hx2> Ha1))
      (have <b2> (elem x (diff s3 s2))
            :by (p/and-intro <Hx1> <b1>))
      (have <b> (elem x (union (diff s3 s1) (diff s3 s2)))
            :by (p/or-intro-right (elem x (diff s3 s1)) <b2>)))
    (assume [Ha1' (not (elem x s1))]
      (have <c1> (elem x (diff s3 s1))
            :by (p/and-intro <Hx1> Ha1'))
      (have <c> (elem x (union (diff s3 s1) (diff s3 s2)))
            :by (p/or-intro-left <c1> (elem x (diff s3 s2)))))
    (have <a> (elem x (union (diff s3 s1) (diff s3 s2)))
          :by (p/or-elim <a1> <b> <c>)))

  "Superset case"
  (assume [x T
           Hx (elem x (union (diff s3 s1) (diff s3 s2)))]
    (assume [Hx1 (elem x (diff s3 s1))]
      (have <d1> (elem x s3) :by (p/and-elim-left Hx1))
      (have <d2> (not (elem x s1)) :by (p/and-elim-right Hx1))
      (have <d3> (not (elem x (inter s1 s2)))
            :by ((inter-not-left s1 s2 x) <d2>))
      (have <d> (elem x (diff s3 (inter s1 s2)))
            :by (p/and-intro <d1> <d3>)))
    (assume [Hx1' (elem x (diff s3 s2))]
      (have <e1> (elem x s3) :by (p/and-elim-left Hx1'))
      (have <e2> (not (elem x s2)) :by (p/and-elim-right Hx1'))
      (have <e3> (not (elem x (inter s1 s2)))
            :by ((inter-not-right s1 s2 x) <e2>))
      (have <e> (elem x (diff s3 (inter s1 s2)))
            :by (p/and-intro <e1> <e3>)))
    (have <f> (elem x (diff s3 (inter s1 s2)))
          :by (p/or-elim Hx <d> <e>)))
  
  (qed (p/and-intro <a> <f>)))

(defthm diff-union
  [[?T :type] [s1 s2 s3 (set T)]]
  (seteq (diff s3 (union s1 s2))
         (inter (diff s3 s1) (diff s3 s2))))

(proof 'diff-union-thm
  "Subset case"
  (assume [x T
           Hx (elem x (diff s3 (union s1 s2)))]
    (have <Hx1> (elem x s3) :by (p/and-elim-left Hx))
    (have <Hx2> (not (elem x (union s1 s2))) :by (p/and-elim-right Hx))
    (have <a1> (not (elem x s1)) :by ((union-not-left s1 s2 x) <Hx2>))
    (have <a2> (elem x (diff s3 s1)) :by (p/and-intro <Hx1> <a1>))
    (have <a3> (not (elem x s2)) :by ((union-not-right s1 s2 x) <Hx2>))
    (have <a4> (elem x (diff s3 s2)) :by (p/and-intro <Hx1> <a3>))
    (have <a> _ :by (p/and-intro <a2> <a4>)))
  "Superset case"
  (assume [x T
           Hx (elem x (inter (diff s3 s1) (diff s3 s2)))]
    (have <b> (elem x s3) :by (p/and-elim-left (p/and-elim-left Hx)))
    "By contradiction"
    (assume [Hcontra (elem x (union s1 s2))]
      (assume [Hs1 (elem x s1)]
        (have <c> p/absurd :by ((p/and-elim-right (p/and-elim-left Hx)) Hs1)))
      (assume [Hs2 (elem x s2)]
        (have <d> p/absurd :by ((p/and-elim-right (p/and-elim-right Hx)) Hs2)))
      (have <e> p/absurd :by (p/or-elim Hcontra <c> <d>)))
    (have <f> (elem x (diff s3 (union s1 s2)))
          :by (p/and-intro <b> <e>)))
  (qed (p/and-intro <a> <f>)))

(defthm diff-empty-right
  [?T :type, s (set T)]
  (seteq (diff s (emptyset T)) s))

(proof 'diff-empty-right-thm
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
  [?T :type, s (set T)]
  (seteq (diff (emptyset T) s) (emptyset T)))

(proof 'diff-empty-left-thm
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
  [?T :type, s (set T)]
  (seteq (diff s s) (emptyset T)))

(proof 'diff-cancel-thm
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

(definition symdiff
  "Symmetric difference, often denoted by `s1`∆`s2`."
  [?T :type, [s1 s2 (set T)]]
  (lambda [x T]
    (or (and (elem x s1) (not (elem x s2)))
        (and (elem x s2) (not (elem x s1))))))

(defthm symdiff-alt
  "An alternative caracterisation of the symmetric difference."
  [?T :type, [s1 s2 (set T)]]
  (seteq (symdiff s1 s2)
         (union (diff s1 s2)
                (diff s2 s1))))

(proof 'symdiff-alt-thm
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

(definition complement
  "The complement of set `s`.

Note that the definition is more self-contained
in type theory than with classical sets. The complement
is here wrt. a type `T` which is well defined,
 wherease in classical set theory one has to introduce
a somewhat unsatisfying notion of \"a universe of discourse\"."
  [?T :type, [s (set T)]]
  (set-of [x T]
          (not (elem x s))))

(defthm comp-full-empty
  [T :type]
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
  [T :type]
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






