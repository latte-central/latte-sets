(ns latte-sets.pfun
  "Partial functions are defined in this namespace as
  relations (in the type theoretic sense) of type
  `(==> T U :type)` together with a domain `dom` of type `(set T)`
  and a codomain `cod` of type `(set U)`
   such that for any element of the domain there is a unique
  image in the codomain.

  **Remark**: in type theory, it is best to rely on total functions because
  these are 'native' through the function type `==>`. 
  Partial functions are encoded and thus more complex and less 'natural', however
  there are needed for many related (and set-theoretic) concepts (e.g. finite sets)."

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm try-defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof try-proof qed lambda]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and and* or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.fun :as fun]
            [latte-prelude.classic :as classic]

            [latte-sets.set :as s :refer [set set-of elem seteq subset]]
            [latte-sets.quant :as sq :refer [exists-in forall-in]]
            [latte-sets.algebra :as sa]
            [latte-sets.rel :as rel :refer [rel dom ran]]
            [latte-sets.ralgebra :as ra]
            [latte-sets.powerrel :as prel :refer [rel-ex]]))

(definition functional
  "The relation `f` is functional (a.k.a. single-valued) 
on the domain-set `from`  and range set `to`."
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (forall-in [x from]
    (sq/single-in to (lambda [y U] (f x y)))))


(defn fetch-functional-type [def-env ctx t]
  (latte.utils/decomposer
   (fn [t]
     (if (clojure.core/and (seq? t)
                           (= (count t) 5)
                           (= (first t) #'latte-sets.pfun/functional-def))
       (into [] (rest t))
       (throw (ex-info "Not a functional type." {:type t}))))
   def-env ctx t))

(defthm functional-elim
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (functional f from to)
       (forall-in [x from]
         (forall-in [y1 to]
           (forall-in [y2 to]
             (==> (f x y1)
                  (f x y2)
                  (equal y1 y2)))))))

(proof 'functional-elim-thm
  (assume [Hfun (functional f from to)
           x T Hx (elem x from)
           y1 U Hy1 (elem y1 to)
           y2 U Hy2 (elem y2 to)
           Hfy1 (f x y1)
           Hfy2 (f x y2)]
   (have <a> (sq/single-in to (lambda [$ U] (f x $)))
         :by (Hfun x Hx))

   (have <b> (equal y1 y2) 
         :by ((sq/single-in-elim <a> y1 y2)
              Hy1 Hy2 Hfy1 Hfy2)))
  (qed <b>))



(defthm ridentity-functional
  "The identity relation is a partial function on
any domain set."
  [[?T :type] [from to (set T)]]
  (functional (rel/identity T) from to))

(proof 'ridentity-functional-thm
  (pose rid := (rel/identity T))
  (assume [x T Hx (elem x from)]
    (assume [y1 T Hy1 (elem y1 to)
             y2 T Hy2 (elem y2 to)
             Hid1 (rid x y1)
             Hid2 (rid x y2)]
      (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hid1) Hid2)))
    (have <b> _ :by ((sq/single-in-intro to (lambda [y T] (rid x y))) <a>)))
  (qed <b>))

(defthm emptyrel-functional
  [[?T ?U :type] [from (set T)] [to (set U)]]
  (functional (rel/emptyrel T U) from to))

(proof 'emptyrel-functional-thm
  (pose rempty := (rel/emptyrel T U))
  (assume [x T Hx (elem x from)]
    (assume [y1 U Hy1 (elem y1 to)
             y2 U Hy2 (elem y2 to)
             Hid1 (rempty x y1)
             Hid2 (rempty x y2)]
      (have <a1> p/absurd :by Hid1)
      (have <a> (equal y1 y2) :by (<a1> (equal y1 y2))))
    (have <b> _ :by ((sq/single-in-intro to (lambda [y U] (rempty x y))) <a>)))
  (qed <b>))

(definition removal
  "The removal of an element `a` in a relation/function `f`"
  [[?T ?U :type] [f (rel T U)] [from (set T)] [a T]]
  (lambda [x T] 
    (lambda [y U]
      (and* (elem a from)
            (elem x from)
            (not (equal x a))
            (f x y)))))

(defthm removal-functional
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (functional f from to)
       (forall-in [y to]
         (==> (f a y)
              (functional (removal f from a) (s/remove a from) (s/remove y to))))))
           
(proof 'removal-functional-thm
  (pose RF := (removal f from a))
  (assume [Hfun (functional f from to)
           y U Hy (elem y to)
           Hfy (f a y)] ; Note: this is not used for functionality (because it's just existential)
                        ; but the theorem doesn't mean much if we don't touch the codomain
    (assume [x T Hx (elem x (s/remove a from))]
      "To show : (sq/single-in (s/remove to y) (lambda [z U] (RF x z)))"
      (assume [y1 U Hy1 (elem y1 (s/remove y to))
               y2 U Hy2 (elem y2 (s/remove y to))
               HRFy1 (RF x y1)
               HRFy2 (RF x y2)]
        "To show : (equal y1 y2)"
        (have <a1> (elem y1 to) :by (p/and-elim-right Hy1))
        (have <b1> (f x y1) :by (p/and-elim* 4 HRFy1))
        (have <a2> (elem y2 to) :by (p/and-elim-right Hy2))
        (have <b2> (f x y2) :by (p/and-elim* 4 HRFy2))
        (have <c1> (elem x from) :by (p/and-elim-right Hx))
        (have <c> (sq/single-in to (lambda [y U] (f x y))) :by (Hfun x <c1>))
        (have <d> (equal y1 y2)
              :by ((sq/single-in-elim <c> y1 y2)
                   <a1> <a2> <b1> <b2>)))
      (have <e> _ :by ((sq/single-in-intro (s/remove y to) (lambda [z U] (RF x z))) <d>))))
  (qed <e>))

(definition functional-fun
  "The \"partial\" function of a (total) type-theoretic function `f` on its whole domain"
  [[?T ?U :type] [f (==> T U)]]
  (lambda [x T]
    (lambda [y U]
      (equal (f x) y))))

(defthm functional-fun-prop
  "A type-theoretic function `f` is a partial function for any domain
restriction."
  [[?T ?U :type], f (==> T U)]
  (forall [from (set T)]
    (forall [to (set U)]
      (functional (functional-fun f) from to))))

(proof 'functional-fun-prop-thm
  (pose pf := (functional-fun f))
  (assume [from (set T) to (set U)
           x T Hx (elem x from)]
    (assume [y1 U Hy1 (elem y1 to)
             y2 U Hy2 (elem y2 to)
             Hpfy1 (pf x y1)
             Hpfy2 (pf x y2)]
      (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hpfy1) Hpfy2)))
    (have <b> _ :by ((sq/single-in-intro to (lambda [y U] (pf x y))) <a>)))
  (qed <b>))

(definition domain
  "The actual domain of relation `f`, taking antecedents in `from`.
It is sometimes called the active domain of `f`."
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (set-of [x T] (and (elem x from)
                     (sq/exists-in [y to] (f x y)))))

(definition image
  "The image of set `from` through relation `f`. This is also
sometimes called the *range* or *codomain* but image is less ambiguous
(especially in type theory)."
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (set-of [y U] (and (elem y to)
                     (exists-in [x from] (f x y)))))

(defthm image-subset
  [[?T ?U :type] [f (rel T U)] [s1 (set T)]  [s2 (set U)]]
  (subset (image f s1 s2) s2))

(proof 'image-subset-thm
  (assume [y U
           Hy (elem y (image f s1 s2))]
    (have <a> (elem y s2) :by (p/and-elim-left Hy)))
  (qed <a>))

(defthm image-subset-monotonous
  [[?T :type] [?U :type] [f (rel T U)] [s1 (set T)] [s2 (set T)] [sran (set U)]]
  (==> (subset s1 s2)
       (subset (image f s1 sran) (image f s2 sran))))

(proof 'image-subset-monotonous-thm
  (assume [H (subset s1 s2)]
    (assume [y U
             Hy (elem y (image f s1 sran))]
      "We have to prove y ∈ f[s2]"
      (have <a> (elem y sran) :by (p/and-elim-left Hy))
      (assume [x T
               Hx (elem x s1)
               Hfx (f x y)]
        (have <b1> (elem x s2) :by (H x Hx))
        (have <b2> (exists-in [x' s2] (f x' y))
              :by ((sq/ex-in-intro s2 (lambda [x' T] (f x' y)) x) <b1> Hfx)))
      (have <b3> (exists-in [x s1] (f x y)) :by (p/and-elim-right Hy))
      (have <b> (exists-in [x' s2] (f x' y))
            :by (sq/ex-in-elim <b3> <b2>))
      (have <c> (elem y (image f s2 sran))
            :by (p/and-intro <a> <b>))))
  (qed <c>))

(definition serial
  "The relation `f` covers all of (is total wrt.) the provided `from` domain set."
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (forall-in [x from]
    (exists-in [y to]
      (f x y))))

(definition serial-alt
  "Alternative definition for [[serial]]."
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (seteq (domain f from to) from))

(defthm serial-serial-alt
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (==> (serial f from to)
       (serial-alt f from to)))

(proof 'serial-serial-alt-thm
  (assume [Htot (serial f from to)]
    "First the subset direction."
    (assume [x T Hx (elem x (domain f from to))]
      "We have to prove that `x` is in `from`."
      (have <a> (elem x from) :by (p/and-elim-left Hx)))
    "Second the superset direction."
    (assume [x T Hx (elem x from)]
      "We have to prove that `x` is in `(domain f from)`"
      (have <b1> (exists-in [y to] (f x y)) :by (Htot x Hx))
      (have <b> (elem x (domain f from to)) :by (p/and-intro Hx <b1>)))
    "Deduce set-equality."
    (have <c> (seteq (domain f from to) from) :by (p/and-intro <a> <b>)))
  (qed <c>))
      
(defthm serial-alt-serial
  [[?T ?U :type], f (rel T U), from (set T), to (set U)]
  (==> (serial-alt f from to)
       (serial f from to)))

(proof 'serial-alt-serial-thm
  (assume [Htot (serial-alt f from to)]
    (assume [x T Hx (elem x from)]
      (have <a> (elem x (domain f from to)) 
            :by ((p/and-elim-right Htot) x Hx))
      (have <b> (exists-in [y to] (f x y))
            :by (p/and-elim-right <a>))))
  (qed <b>))

(comment

  ;; this needs to be updated with explicit range `to`

(defthm functional-fun-serial
  "A type-theoretic function `f` is always serial."
  [[?T ?U :type], f (==> T U)]
  (forall [from (set T)]
    (forall [to (set U)]
      (serial (functional-fun f) from (image (functional-fun f) from to)))))

(proof 'functional-fun-serial-thm
  (pose rf := (functional-fun f))
  ?
)

)

(defthm ridentity-serial
  [[?T :type] [s (set T)]]
  (serial (rel/identity T) s s))

(proof 'ridentity-serial-thm
  (assume [x T Hx (elem x s)]
    (have <a> ((rel/identity T) x x) :by (eq/eq-refl x))
    (have <b> (sq/exists-in [y s] ((rel/identity T) x y))
          :by ((sq/ex-in-intro s (lambda [$ T] ((rel/identity T) x $)) x) Hx <a>)))
  (qed <b>))

(defthm emptyrel-serial
  [[T U :type] [to (set U)]]
  (serial (rel/emptyrel T U) (s/emptyset T) to))

(proof 'emptyrel-serial
  (assume [x T Hx (elem x (s/emptyset T))]
    (have <a> p/absurd :by Hx)
    (have <b> _ :by (Hx (exists-in [y to] ((rel/emptyrel T U) x y)))))
  (qed <b>))


(definition single-rooted
  "A relation `R` is single-rooted if pre-images are unique."
  [[?T ?U :type] [R (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [y to]
    (sq/single-in from (lambda [x T] (R x y)))))

(defthm rel-functional-rinverse-single-rooted
  [[?T ?U :type] [R (rel T U)] [from (set T)] [to (set U)]]
  (==> (functional R from to)
       (single-rooted (ra/rinverse R) to from)))

(proof 'rel-functional-rinverse-single-rooted-thm
  (assume [Hfun _]
    (assume [x T Hx (elem x from)]
      (assume [y1 U Hy1 (elem y1 to)
               y2 U Hy2 (elem y2 to)
               HRy1 ((ra/rinverse R) y1 x)
               HRy2 ((ra/rinverse R) y2 x)]
        "We have to show: y1=y2"
        (have <a> (R x y1) :by HRy1)
        (have <b> (R x y2) :by HRy2)
        (have <c> (equal y1 y2) 
              :by ((sq/single-in-elim (Hfun x Hx) y1 y2) Hy1 Hy2 <a> <b>)))
      (have <d> _ :by ((sq/single-in-intro to (lambda [y U] ((ra/rinverse R) y x))) <c>))))
  (qed <d>))

(defthm rinverse-functional-rel-single-rooted
  [[?T ?U :type] [R (rel T U)] [from (set T)] [to (set U)]]
  (==> (functional (ra/rinverse R) to from)
       (single-rooted R from to)))

(proof 'rinverse-functional-rel-single-rooted-thm
  (assume [Hfun _]
    (have <a> (single-rooted (ra/rinverse (ra/rinverse R)) from to)
          :by ((rel-functional-rinverse-single-rooted (ra/rinverse R) to from) Hfun))

    (have <b> (single-rooted R from to)
          :by ((rel/rel-equal-prop (ra/rinverse (ra/rinverse R)) R
                                   (lambda [X (rel T U)] (single-rooted X from to)))
               (ra/rinverse-idem-prop R)
               <a>)))
  (qed <b>))

(defthm rinverse-single-rooted-rel-functional
  [[?T ?U :type] [R (rel T U)] [from (set T)] [to (set U)]]
  (==> (single-rooted (ra/rinverse R) to from)
       (functional R from to)))

(proof 'rinverse-single-rooted-rel-functional-thm
  (assume [Hsr _]
    (assume [x T Hx (elem x from)]
      (assume [y1 U Hy1 (elem y1 to)
               y2 U Hy2 (elem y2 to)
               HRy1 (R x y1)
               HRy2 (R x y2)]
        (have <a> (equal y1 y2)
              :by ((sq/single-in-elim (Hsr x Hx) y1 y2) Hy1 Hy2 HRy1 HRy2)))
      (have <b> _ :by ((sq/single-in-intro to (lambda [y U] (R x y))) <a>))))
  (qed <b>))

(defthm rel-single-rooted-rinverse-functional
  [[?T ?U :type] [R (rel T U)] [from (set T)] [to (set U)]]
  (==> (single-rooted R from to)
       (functional (ra/rinverse R) to from)))

(proof 'rel-single-rooted-rinverse-functional-thm
  (assume [Hsr _]
    (have <a> (single-rooted (ra/rinverse (ra/rinverse R)) from to)
          :by ((rel/rel-equal-prop R (ra/rinverse (ra/rinverse R)) (lambda [X (rel T U)] (single-rooted X from to)))
               (ra/rinverse-idem-prop-sym R)
               Hsr))
    (have <b> (functional (ra/rinverse R) to from)
          :by ((rinverse-single-rooted-rel-functional (ra/rinverse R) to from) <a>)))
  (qed <b>))


(definition pfcomp
  "Partial composition of relations `f` and `g`
(implicitly assumed as partial functions) on domain `from` and range `to`.
Since this is based on relational composition, we use the left-to-right
composition, i.e. `f ; g`."
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)] [to (set V)]]
  (lambda [x T]
    (lambda [z V]
      (and* (elem x from)
            (elem z to)
            (exists-in [y (sa/inter (ran f) (dom g))]
              (and (f x y)
                   (g y z)))))))
  
(defthm pfcomp-functional
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)] [to (set V)]]
  (==> (functional f from (ran f))
       (functional g (sa/inter (ran f) (dom g)) to)
       (functional (pfcomp f g from to) from to)))

;; proof scheme
;;  forall-in [x from], forall-in [z1 z2 to], (f<;>g x z1) /\ (f<;>g x z2) ==> z1=z2
;;  (f<;>g x y1)  <=>  x \in from, z1 \in to,  ex [y1 (ran f) \inter (dom g)] s.t. (f x y1) /\ (g y1 z1) 
;;  (f<;>g x y2)  <=>  x \in from, z2 \in to,  ex [y2 (ran f) \inter (dom g)] s.t. (f x y2) /\ (g y2 z2) 
;;  since f is functional, we have that y1 = y2
;;  theb since g is functional, we have z1 = z2  (Qed)

(proof 'pfcomp-functional-thm
  (assume [Hf _
           Hg _]
    (assume [x T
             Hx (elem x from)]
      (assume [z1 V Hz1 (elem z1 to) 
               z2 V Hz2 (elem z2 to)
               HPz1 ((pfcomp f g from to) x z1)
               HPz2 ((pfcomp f g from to) x z2)]
      
        "We have to show that z1=z2"
        
        (have <a1> (sq/single-in (ran f) (lambda [y U] (f x y))) :by (Hf x Hx))
        
        (have <a2> (exists-in [y1 (sa/inter (ran f) (dom g))]
                     (and (f x y1) (g y1 z1)))
              :by (p/and-elim* 3 HPz1))
        
        (have <a3> (exists-in [y2 (sa/inter (ran f) (dom g))]
                     (and (f x y2) (g y2 z2)))
              :by (p/and-elim* 3 HPz2))
        
        "We, will eliminate the two facts above, in turn"
        
        (assume [y1 U Hy1 (elem y1 (sa/inter (ran f) (dom g)))
                 HPy1 (and (f x y1) (g y1 z1))]
          (assume [y2 U Hy2 (elem y2 (sa/inter (ran f) (dom g)))
                   HPy2 (and (f x y2) (g y2 z2))]
            
            (have <b1> (elem y1 (ran f)) :by ((sa/inter-elim-left (ran f) (dom g) y1) Hy1))
            (have <b2> (elem y2 (ran f)) :by ((sa/inter-elim-left (ran f) (dom g) y2) Hy2))
            (have <b3> (f x y1) :by (p/and-elim-left HPy1))
            (have <b4> (f x y2) :by (p/and-elim-left HPy2))
            
            (have <b> (equal y1 y2) :by 
                  ((sq/single-in-elim <a1> y1 y2)
                   <b1> <b2> <b3> <b4>))
            
            (have <c1> (sq/single-in to (lambda [z V] (g y1 z))) 
                  :by (Hg y1 Hy1))
            
            (have <c2> (g y1 z1) :by (p/and-elim-right HPy1))
            (have <c3> (g y1 z2)
                  :by (eq/eq-subst (lambda [y U] (g y z2)) (eq/eq-sym <b>) (p/and-elim-right HPy2)))
            
            (have <c> (equal z1 z2)
                  :by ((sq/single-in-elim <c1> z1 z2)
                       Hz1 Hz2 <c2> <c3>)))
          
          (have <d> (equal z1 z2)
                :by (sq/ex-in-elim <a3> <c>)))
        
        (have <e> (equal z1 z2)
              :by (sq/ex-in-elim <a2> <d>)))
      
      (have <f> _ :by ((sq/single-in-intro to (lambda [z V] ((pfcomp f g from to) x z)))
                       <e>)))

    (have <g> _ :by <f>))
  
  (qed <g>))     


(defthm pfcomp-serial
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)] [to (set V)]]
  (==> (serial f from (sa/inter (ran f) (dom g)))
       (serial g (sa/inter (ran f) (dom g)) to)
       (serial (pfcomp f g from to) from to)))

(proof 'pfcomp-serial-thm
  (assume [Hf _
           Hg _]
    (assume [x T
             Hx (elem x from)]
      "We have to show that there is a `z` in `to` such that (f<;>g x z)"

      (have <a> (exists-in [y (sa/inter (ran f) (dom g))] (f x y)) :by (Hf x Hx))

      (assume [y U Hy (elem y (sa/inter (ran f) (dom g)))
               Hfy (f x y)]

        (have <b> (exists-in [z to] (g y z)) :by (Hg y Hy))

        (assume [z V Hz (elem z to)
                 Hgz (g y z)]

          (have <c> (and (f x y) (g y z)) :by (p/and-intro Hfy Hgz))

          (have <d> _ :by ((sq/ex-in-intro (sa/inter (ran f) (dom g))
                                           (lambda [$ U] (and (f x $) (g $ z))) y)
                           Hy <c>))

          (have <e> ((pfcomp f g from to) x z)
                :by (p/and-intro* Hx Hz <d>))

          (have <f> _ :by ((sq/ex-in-intro to (lambda [$ V] ((pfcomp f g from to) x $)) z)
                           Hz <e>)))

        (have <g> _ :by (sq/ex-in-elim <b> <f>)))

      (have <h> _ :by (sq/ex-in-elim <a> <g>)))

    (have <i> (serial (pfcomp f g from to) from to) :by <h>))

  (qed <i>))

(definition injective
  "The relation `f` is injective wrt. domain set `from`
and range set `to`. 

Note that this notion of injectivity is about
comparing sets, not types. Here, the actual meaning is that
`s1` is less than `s2`.

Also, the relation is not constrained to be e.g. [[functional]]
 or [[serial]] (and in practice these are frequent although
 not always required assumptions.)."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x1 from]
    (forall-in [x2 from]
      (forall-in [y1 to]
        (forall-in [y2 to]
          (==> (f x1 y1)
               (f x2 y2)
               (equal y1 y2)
               (equal x1 x2)))))))

(defthm injective-contra
  "The contrapositive of [[injective]], useful for
proofs by contradiction."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (injective f from to)
       (forall-in [x1 from]
         (forall-in [x2 from]
           (forall-in [y1 to]
             (forall-in [y2 to]
               (==> (f x1 y1)
                    (f x2 y2)
                    (not (equal x1 x2))
                    (not (equal y1 y2)))))))))

(proof 'injective-contra-thm
  (assume [Hinj (injective f from to)]
    (assume [x1 T Hx1 (elem x1 from)
             x2 T Hx2 (elem x2 from)
             y1 U Hy1 (elem y1 to)
             y2 U Hy2 (elem y2 to)
             Hfy1 (f x1 y1)
             Hfy2 (f x2 y2)
             Hneq (not (equal x1 x2))]
      (assume [Heq (equal y1 y2)]
        (have <a> (equal x1 x2) 
              :by (Hinj x1 Hx1 x2 Hx2 y1 Hy1 y2 Hy2 Hfy1 Hfy2 Heq))
        (have <b> p/absurd :by (Hneq <a>)))))
  (qed <b>))

(defthm ridentity-injective
  [[?T :type] [s (set T)]]
  (injective (rel/identity T) s s))

(proof 'ridentity-injective-thm
  (pose rid := (rel/identity T))
  (assume [x1 T Hx1 (elem x1 s)
           x2 T Hx2 (elem x2 s)
           y1 T Hy1 (elem y1 s)
           y2 T Hy2 (elem y2 s)
           Hr1 (rid x1 y1)
           Hr2 (rid x2 y2)
           Heqy (equal y1 y2)]
    (have <a> (equal y2 x2) :by (eq/eq-sym Hr2))
    (have <b> (equal x1 x2) :by (eq/eq-trans* Hr1 Heqy <a>)))
  (qed <b>))

(defthm emptyrel-injective
  [[?T ?U :type] [from (set T)] [to (set U)]]
  (injective (rel/emptyrel T U) from to))

(proof 'emptyrel-injective-thm
  (pose rempty := (rel/emptyrel T U))
  (assume [x1 T Hx1 (elem x1 from)
           x2 T Hx2 (elem x2 from)
           y1 U Hy1 (elem y1 to)
           y2 U Hy2 (elem y2 to)
           Hr1 (rempty x1 y1)
           Hr2 (rempty x2 y2)
           Heqy (equal y1 y2)]

    (have <a> p/absurd :by Hr1)
    (have <b> _ :by (Hr1 (equal x1 x2))))

  (qed <b>))

(defthm removal-serial
  "Seriality of removal operation, which requires injectivity."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (serial f from to)
       (injective f from to)
       (forall-in [y to]
         (==> (elem a from)
              (f a y)
              (serial (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-serial-thm
  (pose RF := (removal f from a))
  (assume [Hser (serial f from to)
           Hinj (injective f from to)
           y U Hy (elem y to)
           Ha (elem a from)
           Hfy (f a y)]
    (assume [x T Hx (elem x (s/remove a from))]
      "To show: (exists-in [z (s/remove to y)] (RF x z))"
      (have <a> (elem x from) :by (p/and-elim-right Hx))
      (have <b> (exists-in [z to] (f x z)) :by (Hser x <a>))
      (assume [z U Hz (elem z to)
               Hfz (f x z)]
        ;; we have to show that (elem z (s/remove to y)))
        ;; and for this we need to show that z≠y, which is thanks to the injectivity of f
        (have <c> (not (equal x a)) :by (p/and-elim-left Hx))
        (have <d> (not (equal z y)) 
              :by ((injective-contra f from to)
                   Hinj x <a> a Ha z Hz y Hy Hfz Hfy <c>))
        (have <e> (elem z (s/remove y to)) :by (p/and-intro <d> Hz))
        ;; also we need to show that (RF x z)  which is easy now
        (have <f> (RF x z) :by (p/and-intro* Ha <a> <c> Hfz))

        (have <g> _ :by ((sq/ex-in-intro (s/remove y to) (lambda [$ U] (RF x $)) z)
                         <e> <f>)))
      (have <h> (exists-in [z (s/remove y to)] (RF x z))
            :by (sq/ex-in-elim <b> <g>)))

    (have <i> (serial (removal f from a) (s/remove a from) (s/remove y to))
          :by <h>))

  (qed <i>))

(defthm removal-injective
  "Injectivity of removal operation."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (injective f from to)
       (forall-in [y to]
         (==> (f a y)
              (injective (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-injective-thm
  (pose RF := (removal f from a))
  (assume [Hinj (injective f from to)
           y U Hy (elem y to)
           Hfy (f a y)] ;; Note: unused hypothesis (because the codomain is not observed)
    (assume [x1 T Hx1 (elem x1 (s/remove a from))
             x2 T Hx2 (elem x2 (s/remove a from))
             y1 U Hy1 (elem y1 (s/remove y to))
             y2 U Hy2 (elem y2 (s/remove y to))
             HRF1 (RF x1 y1)
             HRF2 (RF x2 y2)
             Heq (equal y1 y2)]
      "To show: (equal x1 x2)"
      "We want to apply the injectivity of f"
      (have <a> (elem x1 from) :by (p/and-elim-right Hx1))
      (have <b> (elem x2 from) :by (p/and-elim-right Hx2))
      (have <c> (elem y1 to) :by (p/and-elim-right Hy1))
      (have <d> (elem y2 to) :by (p/and-elim-right Hy2))
      (have <e> (f x1 y1) :by (p/and-elim* 4 HRF1))
      (have <f> (f x2 y2) :by (p/and-elim* 4 HRF2))
      (have <g> (equal x1 x2) :by (Hinj x1 <a> x2 <b> y1 <c> y2 <d> <e> <f> Heq))))

  (qed <g>))


(defthm injective-single-rooted
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (injective f from to)
       (single-rooted f from to)))

(proof 'injective-single-rooted-thm
  (assume [Hinj _]
    (assume [y U Hy (elem y to)]
;; need to show   (sq/single-in from (lambda [x T] (f x y))))
      (assume [x1 T Hx1 (elem x1 from)
               x2 T Hx2 (elem x2 from)
               Hfx1 (f x1 y)
               Hfx2 (f x2 y)]
        "We need to show that x1=x2"
        (have <a> (equal x1 x2)
              :by (Hinj x1 Hx1 x2 Hx2 y Hy y Hy Hfx1 Hfx2 (eq/eq-refl y))))
      (have <b> _ :by ((sq/single-in-intro from (lambda [x T] (f x y)))
                       <a>))))
  (qed <b>))

(defthm single-rooted-injective
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (single-rooted f from to)
       (injective f from to)))

(proof 'single-rooted-injective-thm
  (assume [Hsr _]
    (assume [x1 T Hx1 (elem x1 from)
             x2 T Hx2 (elem x2 from)
             y1 U Hy1 (elem y1 to)
             y2 U Hy2 (elem y2 to)
             Hf1 (f x1 y1)
             Hf2 (f x2 y2)
             Heq (equal y1 y2)]
      "We have to show that x1=x2"
      (have <a> (sq/single-in from (lambda [x T] (f x y1))) :by (Hsr y1 Hy1))
      (have <b> (f x2 y1) :by (eq/eq-subst (lambda [$ U] (f x2 $)) (eq/eq-sym Heq) Hf2))

      (have <c> (equal x1 x2) :by ((sq/single-in-elim <a> x1 x2)
                                   Hx1
                                   Hx2
                                   Hf1
                                   <b>))))
  (qed <c>))

(defthm function-rinverse-injective
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (functional f from to)
       (injective (ra/rinverse f) to from)))

(proof 'function-rinverse-injective-thm
  (assume [Hfun _]
    (have <a> (single-rooted (ra/rinverse f) to from) 
          :by ((rel-functional-rinverse-single-rooted f from to) Hfun))
    (have <b> (injective (ra/rinverse f) to from)
          :by ((single-rooted-injective (ra/rinverse f) to from) <a>)))
  (qed <b>))

(defthm injective-rinverse-functional
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (injective f from to)
       (functional (ra/rinverse f) to from)))

(proof 'injective-rinverse-functional-thm
  (assume [Hinj _]
    (have <a> (single-rooted f from to) 
          :by ((injective-single-rooted f from to) Hinj))
    (have <b> (functional (ra/rinverse f) to from) 
          :by ((rel-single-rooted-rinverse-functional f from to) <a>)))
  (qed <b>))

(defthm pfcomp-injective
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)] [to (set V)]]
  (==> (injective f from (sa/inter (ran f) (dom g)))
       (injective g (sa/inter (ran f) (dom g)) to)
       (injective (pfcomp f g from to) from to)))

(try-proof 'pfcomp-injective-thm
  (assume [Hf _
           Hg _]
    (assume [x1 T Hx1 (elem x1 from)
             x2 T Hx2 (elem x2 from)
             z1 V Hz1 (elem z1 to)
             z2 V Hz2 (elem z2 to)
             Hpfz1 ((pfcomp f g from to) x1 z1)
             Hpfz2 ((pfcomp f g from to) x2 z2)
             Heq (equal z1 z2)]
      "We have to prove x1=x2"
     
      (have <a1> (exists-in [y1 (sa/inter (ran f) (dom g))]
                   (and (f x1 y1) (g y1 z1)))
            :by (p/and-elim* 3 Hpfz1))

      (have <a2> (exists-in [y2 (sa/inter (ran f) (dom g))]
                   (and (f x2 y2) (g y2 z2)))
            :by (p/and-elim* 3 Hpfz2))

      (assume [y1 U Hy1 (elem y1 (sa/inter (ran f) (dom g)))
               Hpfy1 (and (f x1 y1) (g y1 z1))]

        (assume [y2 U Hy2 (elem y2 (sa/inter (ran f) (dom g)))
                 Hpfy2 (and (f x2 y2) (g y2 z2))]

          (have <b1> (g y1 z1) :by (p/and-elim-right Hpfy1))
          (have <b2> (g y2 z2) :by (p/and-elim-right Hpfy2))

          (have <b> (equal y1 y2)
                :by (Hg y1 Hy1 y2 Hy2 z1 Hz1 z2 Hz2 <b1> <b2> Heq))

          (have <c1> (f x1 y1) :by (p/and-elim-left Hpfy1))
          (have <c2> (f x2 y2) :by (p/and-elim-left Hpfy2))

          "done!"
          (have <c> (equal x1 x2)
                :by (Hf x1 Hx1 x2 Hx2 y1 Hy1 y2 Hy2 <c1> <c2> <b>)))

        (have <d> _ :by (sq/ex-in-elim <a2> <c>)))

      (have <e> _ :by (sq/ex-in-elim <a1> <d>)))
    
    (have <f> (injective (pfcomp f g from to) from to) :by <e>))

  (qed <f>))

(definition injection
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (and* (functional f s1 s2)
        (serial f s1 s2)
        (injective f s1 s2)))

(defthm injection-img-inter
  [[?T ?U :type] [g (rel T U)] [A B C (set T)] [D (set U)]]
  (==> (injective g C D)
       (subset A C)
       (subset B C)
       (sa/disjoint A B)
       (sa/disjoint (image g A D) (image g B D))))

(proof 'injection-img-inter-thm
  (assume [Hinj _ HA _ HB _ Hdis _]
    "Subset case"
    "We have to prove g[A]∩g[B]⊆∅"
    (assume [y U
             Hy (and (elem y (image g A D))
                     (elem y (image g B D)))]
      (have <a1> (exists-in [x1 A] (g x1 y))
            :by (p/and-elim-right (p/and-elim-left Hy)))
      (have <a2> (exists-in [x2 B] (g x2 y))
            :by (p/and-elim-right (p/and-elim-right Hy)))
      (assume [x1 T
               Hx1 (and (elem x1 A) (g x1 y))]
        (assume [x2 T
                 Hx2 (and (elem x2 B) (g x2 y))]
          (have <a3> (elem x1 C) :by (HA x1 (p/and-elim-left Hx1)))
          (have <a4> (elem x2 C) :by (HB x2 (p/and-elim-left Hx2)))
          (have <a5> (elem y D) :by (p/and-elim-left (p/and-elim-left Hy)))
          (have <a6> (equal x1 x2)
                :by (Hinj 
                     x1 <a3> 
                     x2 <a4> 
                     y <a5>
                     y <a5>
                     (p/and-elim-right Hx1)
                     (p/and-elim-right Hx2)
                     (eq/eq-refl y)))
          (have <a7> (elem x2 A) 
                :by (eq/eq-subst (lambda [$ T] (elem $ A))
                                  <a6> (p/and-elim-left Hx1)))
          (have <a8> p/absurd :by ((sa/disjoint-elem-right A B)
                                   x2
                                   Hdis
                                   (p/and-elim-left Hx2)
                                   <a7>)))
        (have <a9> p/absurd :by (q/ex-elim <a2> <a8>)))
      (have <a10> p/absurd :by (q/ex-elim <a1> <a9>)))
    (have <a> (subset (sa/inter (image g A D) (image g B D)) (s/emptyset U))
          :by <a10>)

    "Superset case is trivial"
    (have <b> (subset (s/emptyset U) (sa/inter (image g A D) (image g B D)))
          :by (s/subset-emptyset-lower-bound (sa/inter (image g A D) (image g B D))))

    (have <c> (sa/disjoint (image g A D) (image g B D))
          :by ((s/seteq-implies-set-equal (sa/inter (image g A D) (image g B D)) (s/emptyset U))
               (p/and-intro <a> <b>))))

  (qed <c>))



(defthm removal-injection
  "Injectivity of removal operation."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (injection f from to)
       (forall-in [y to]
         (==> (elem a from)
              (f a y)
              (injection (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-injection-thm
  (assume [Hinj _
           y U Hy (elem y to)
           Ha (elem a from)
           Hfy (f a y)]
    (have <fun> (functional f from to) :by (p/and-elim* 1 Hinj))
    (have <ser> (serial f from to) :by (p/and-elim* 2 Hinj))
    (have <inj> (injective f from to) :by (p/and-elim* 3 Hinj))

    (have <a> _ :by ((removal-functional f from to a) <fun> y Hy Hfy))
    (have <b> _ :by ((removal-serial f from to a) <ser> <inj> y Hy Ha Hfy))
    (have <c> _ :by ((removal-injective f from to a) <inj> y Hy Hfy))
    (have <d> _ :by (p/and-intro* <a> <b> <c>)))
  (qed <d>))

(definition surjective
  "The relation `f` is surjective onto `s2` for domain `s1`."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (forall-in [y s2]
    (exists-in [x s1]
      (f x y))))

;;; TODO :  if functional and serial (to check), then
;;; the   'to' set is a subset of (image f from)
;;; (or even (image f s1) ...

(defthm surjective-inverse-serial
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (surjective f s1 s2)
       (serial (ra/rinverse f) s2 s1)))

(proof 'surjective-inverse-serial-thm
  (pose rf := (ra/rinverse f))
  (assume [Hsurj (surjective f s1 s2)]
    (assume [y U Hy (elem y s2)]
      (have <a> (exists-in [x s1] (f x y))
            :by (Hsurj y Hy))))

  (qed <a>))

(defthm serial-inverse-surjective
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (serial (ra/rinverse f) s2 s1)
       (surjective f s1 s2)))

(proof 'serial-inverse-surjective-thm
  (assume [Hser _]
    (assume [y U Hy (elem y s2)]
      (have <a> (exists-in [x s1] ((ra/rinverse f) y x))
            :by (Hser y Hy))))
  (qed <a>))

(defthm ridentity-surjective
  [[?T :type] [s (set T)]]
  (surjective (rel/identity T) s s))

(proof 'ridentity-surjective-thm
  (assume [y T Hy (elem y s)]
    (have <a> ((rel/identity T) y y)
          :by (eq/eq-refl y))
    (have <b> (exists-in [x s] ((rel/identity T) x y))
          :by ((sq/ex-in-intro s (lambda [$ T] ((rel/identity T) $ y)) y) Hy <a>)))
  (qed <b>))

(defthm emptyrel-surjective
  [[T U :type] [from (set T)]]
  (surjective (rel/emptyrel T U) from (s/emptyset U)))

(proof 'emptyrel-surjective
  (assume [y U Hy (elem y (s/emptyset U))]
    (have <a> p/absurd :by Hy)
    (have <b> _ :by (Hy (exists-in [x from] ((rel/emptyrel T U) x y)))))
  (qed <b>))

(defthm removal-surjective
  "Surjectivity of removal operation, which also requires functionality."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (surjective f from to)
       (functional f from to)
       (forall-in [y to]
         (==> (elem a from)
              (f a y)
              (surjective (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-surjective-thm
  (pose RF := (removal f from a))
  (assume [Hsur (surjective f from to)
           Hfun (functional f from to)
           y U Hy (elem y to)
           Ha (elem a from)
           Hfy (f a y)]
    (assume [z U Hz (elem z (s/remove y to))]
      "We have to show: (exists-in [x (s/remove from a)] (RF x z))"
      (have <a> (elem z to) :by (p/and-elim-right Hz))
      (have <b> (exists-in [x from] (f x z))
            :by (Hsur z <a>))
      (assume [x T Hx (elem x from)
               Hfxz (f x z)]
        (assume [Hcontra (equal x a)]
          (have <c1> (sq/single-in to (lambda [$ U] (f x $)))
                :by (Hfun x Hx))
          
          (have <c2> (f x y) :by (eq/eq-subst (lambda [$ T] (f $ y)) (eq/eq-sym Hcontra) Hfy))

          (have <c3> (equal z y)
                :by ((sq/single-in-elim <c1> z y)
                     <a> Hy Hfxz <c2>))
          (have <c> p/absurd :by ((p/and-elim-left Hz) <c3>)))
        
        (have <d1> (elem x (s/remove a from)) :by (p/and-intro <c> Hx))
        (have <d2> (RF x z) :by (p/and-intro* Ha Hx <c> Hfxz))
        (have <d> _ :by ((sq/ex-in-intro (s/remove a from) (lambda [$ T] (RF $ z)) x)
                         <d1> <d2>)))

      (have <e> _ :by (sq/ex-in-elim <b> <d>))))

  (qed <e>))

(definition surjection
  "The relation `f` is a functional surjection on-to set `s2`."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (and* (functional f s1 s2)
        (serial f s1 s2)
        (surjective f s1 s2)))

(definition bijective
  "The relation `f` is both [[injective]] and [[bijective]] wrt. sets `s1`
and `s2`. A [[bijection]] needs to be also [[functional]] and [[serial]]."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (and (injective f s1 s2)
       (surjective f s1 s2)))

(comment ;; can this be demonstrated ?
(defthm bijective-inverse-injective
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (bijective f s1 s2)
       (surjective (ra/rinverse f) s2 s1)))

(try-proof 'bijective-inverse-injectve-thm
  (assume [x T Hx (elem x s1)]
    ;; we have to show : ∃y∈s2 (ra/rinverse f) y x
    ))
)

(defthm ridentity-bijective
  [[?T :type] [s (set T)]]
  (bijective (rel/identity T) s s))

(proof 'ridentity-bijective-thm
  (qed (p/and-intro (ridentity-injective s)
                    (ridentity-surjective s))))


(defthm emptyrel-bijective
  [[T U :type] [from (set T)]]
  (bijective (rel/emptyrel T U) from (s/emptyset U)))

(proof 'emptyrel-bijective
  (qed (p/and-intro (emptyrel-injective from (s/emptyset U))
                    (emptyrel-surjective T U from))))


(defthm removal-bijective
  "Bijectivity of removal operation, which also requires functionality."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (bijective f from to)
       (functional f from to)
       (forall-in [y to]
         (==> (elem a from)
              (f a y)
              (bijective (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-bijective-thm
  (assume [Hbij _
           Hfun _
           y U Hy (elem y to)
           Ha (elem a from)
           Hfy (f a y)]
    (have <a> _ :by ((removal-injective f from to a)
                     (p/and-elim-left Hbij) y Hy Hfy))

    (have <b> _ :by ((removal-surjective f from to a)
                     (p/and-elim-right Hbij)
                     Hfun y Hy Ha Hfy))

    (have <c> _ :by (p/and-intro <a> <b>)))

  (qed <c>))


(definition bijection
  "The relation `f` is a bijection between sets `s1` and `s2`."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (and* (functional f s1 s2)
        (serial f s1 s2)
        (bijective f s1 s2)))

(defthm bijection-injective
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (injective f s1 s2))

(proof 'bijection-injective-thm
  (qed (p/and-elim-left (p/and-elim* 3 b))))

(defthm bijection-surjective
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (surjective f s1 s2))

(proof 'bijection-surjective-thm
  (qed (p/and-elim-right (p/and-elim* 3 b))))

 
(defthm injective-single
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (serial f s1 s2) ;; seriality is needed, although not functionality
       (injective f s1 s2)
       (forall-in [z s2]
         (sq/single-in s1 (lambda [x T] (forall-in [w s2] 
                                          (==> (f x w)
                                               (equal w z))))))))

(proof 'injective-single-thm
  (assume [Htot _
           Hinj _
           z U Hz (elem z s2)]
    (pose P := (lambda [x T] (forall-in [w s2]
                               (==> (f x w)
                                    (equal w z)))))
    (assume [x T Hx (elem x s1)
             y T Hy (elem y s1)
             HPx (P x)
             HPy (P y)]
      "We have to show that x equals y"
      (assume [xim U Hxim (elem xim s2)
               Hfxim (f x xim)]
        (have <a1> (equal xim z) :by (HPx xim Hxim Hfxim))
        (have <a2> (f x z) :by (eq/rewrite Hfxim <a1>)))

      ;; Don't know why the following does not work, it's an issue
      ;; with set membership  (elem-def ...)   
      ;;(have <a> (f x z) :by (sq/ex-in-elim (Htot x Hx) <a2>))
      ;; But the explicit variant does
      (have <a> (f x z) :by ((sq/ex-in-elim-rule s2 (lambda [$ U]
                                                      (f x $)) (f x z))
                             (Htot x Hx)
                             <a2>))
      (assume [yim U Hyim (elem yim s2)
               Hfyim (f y yim)]
        (have <b1> (equal yim z) :by (HPy yim Hyim Hfyim))
        (have <b2> (f y z) :by (eq/rewrite Hfyim <b1>)))
      
      ;; Similar issue ...
      ;; (have <b> (f y z) :by (sq/ex-in-elim (Htot y Hy) <b2>))

      (have <b> (f y z) :by ((sq/ex-in-elim-rule s2 (lambda [$ U]
                                                      (f y $)) (f y z))
                             (Htot y Hy)
                             <b2>))

      (have <c> (equal x y) :by (Hinj x Hx y Hy z Hz z Hz <a> <b> (eq/eq-refl z))))
    (have <d> _ :by ((sq/single-in-intro s1 P) <c>)))
  (qed <d>))

(defthm bijective-unique
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (functional f s1 s2)
       (serial f s1 s2)
       (bijective f s1 s2)
       (forall-in [z s2]
         (sq/unique-in s1 (lambda [x T] (forall-in [w s2] 
                                          (==> (f x w)
                                               (equal w z))))))))

(proof 'bijective-unique-thm
  (assume [Hfun _
           Htot _
           Hbij _
           z U Hz (elem z s2)]
    (have Hinj (injective f s1 s2) :by (p/and-elim-left Hbij))
    (have Hsurj (surjective f s1 s2) :by (p/and-elim-right Hbij))
    (pose P := (lambda [x T] (forall-in [w s2]
                               (==> (f x w)
                                    (equal w z)))))
    "First we have to show  that there's an `x` in `s` such as `(P x)`"
    "We exploit surjectivity."
    (assume [x T Hx (elem x s1)
             Hfz (f x z)]
      (have <a0> (sq/single-in s2 (lambda [y U] (f x y))) :by (Hfun x Hx))
      (assume [w U Hw (elem w s2) Hfw (f x w)]
        (have <a1> (equal w z) :by ((sq/single-in-elim <a0> w z) Hw Hz Hfw Hfz)))
      (have <a2> (P x) :by <a1>)
      (have <a3> (exists-in [x s1] (P x)) :by ((sq/ex-in-intro s1 P x) Hx <a2>)))
    (have <a4> (exists-in [x s1] (f x z)) :by (Hsurj z Hz))
    ;; XXX : this does not work if <a4> is inlined within the elimination below
    (have <a> (exists-in [x s1] (P x)) :by (sq/ex-in-elim <a4> <a3>))
    "The second part is thanks to injectivity."
    (have <b> _ :by ((injective-single f s1 s2) Htot Hinj z Hz))
    "The uniqueness follows"
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm bijection-unique
  "The relation `f` is a bijection between sets `s1` and `s2`, 
hence it is *unique*."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (bijection f s1 s2)
       (forall-in [z s2]
         (sq/unique-in s1 (lambda [x T] (forall-in [w s2] 
                                          (==> (f x w)
                                               (equal w z))))))))

(proof 'bijection-unique-thm
  (assume [H _]
    (have <a> _ :by ((bijective-unique f s1 s2)
                     (p/and-elim* 1 H)
                     (p/and-elim* 2 H)
                     (p/and-elim* 3 H))))
  (qed <a>))


(defthm bijective-inverse-functional
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (==> (bijective f s1 s2)
       (functional (ra/rinverse f) s2 s1)))

(proof 'bijective-inverse-functional-thm
  (assume [Hbij (bijective f s1 s2)]
    (have <a> _ :by ((injective-rinverse-functional f s1 s2)
                     (p/and-elim-left Hbij))))
  (qed <a>))

(defthm bijection-inverse-functional
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (functional (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-functional-thm
  (qed ((bijective-inverse-functional f s1 s2)
        (p/and-elim* 3 b))))

(defthm bijection-inverse-serial
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (serial (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-serial-thm
  (qed ((surjective-inverse-serial f s1 s2)
        (p/and-elim-right (p/and-elim* 3 b)))))

(defthm bijection-inverse-injective
  "The inverse of bijective relation `f` is injective."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (injective (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-injective-thm
  (pose rf := (ra/rinverse f))
  (assume [x1 U Hx1 (elem x1 s2)
           x2 U Hx2 (elem x2 s2)
           y1 T Hy1 (elem y1 s1)
           y2 T Hy2 (elem y2 s1)
           Hf1 (rf x1 y1)
           Hf2 (rf x2 y2)
           Heq (equal y1 y2)]
    "We have to prove that x1=x2."
    (have <a1> (f y1 x1) :by Hf1)
    (have <a2> (f y2 x2) :by Hf2)
    (have <a3> (f y2 x1)
          :by (eq/rewrite <a1> Heq)) 
    (have <b> (functional f s1 s2)
          :by (p/and-elim* 1 b))

    (have <c> (sq/single-in s2 (lambda [x U] (f y2 x))) :by (<b> y2 Hy2))
    (have <d> (equal x1 x2)
          :by ((sq/single-in-elim <c> x1 x2) Hx1 Hx2 <a3> <a2>)))

  (qed <d>))

(defthm bijection-inverse-surjective
  "The inverse of bijective relation `f` is surjective."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (surjective (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-surjective-thm
  (pose rf := (ra/rinverse f))
  (assume [y T
           Hy (elem y s1)]
    (have <a> (serial f s1 s2)
          :by (p/and-elim* 2 b))
    (have <c> (exists-in [x s2] (f y x)) :by (<a> y Hy))
    (have <d> (exists-in [x s2] (rf x y)) :by <c>))
  (qed <d>))


(defthm bijection-inverse-bijective
  "The inverse of bijective relation `f` is bijective."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (bijective (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-bijective-thm
  (qed (p/and-intro (bijection-inverse-injective f s1 s2 b)
                    (bijection-inverse-surjective f s1 s2 b))))

(defthm bijection-inverse-bijection
  "The inverse of a bijection is a bijection."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (bijection (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-bijection-thm
  (qed (p/and-intro* (bijection-inverse-functional f s1 s2 b)
                     (bijection-inverse-serial f s1 s2 b)
                     (bijection-inverse-bijective f s1 s2 b))))


(defthm ridentity-bijection
  [[?T :type] [s (set T)]]
  (bijection (rel/identity T) s s))

(proof 'ridentity-bijection-thm
  (qed (p/and-intro* (ridentity-functional s s)
                     (ridentity-serial s)
                     (ridentity-bijective s))))


(defthm emptyrel-bijection
  [[T U :type]]
  (bijection (rel/emptyrel T U) (s/emptyset T) (s/emptyset U)))

(proof 'emptyrel-bijection
  (qed (p/and-intro* (emptyrel-functional (s/emptyset T) (s/emptyset U))
                     (emptyrel-serial T U (s/emptyset U))
                     (emptyrel-bijective T U (s/emptyset T)))))


(defthm removal-bijection
  "Bijectivity of removal operation, which also requires functionality."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)] [a T]]
  (==> (bijection f from to)
       (forall-in [y to]
         (==> (elem a from)
              (f a y)
              (bijection (removal f from a) (s/remove a from) (s/remove y to))))))

(proof 'removal-bijection-thm
  (assume [Hbij (bijection f from to)
           y U Hy (elem y to)
           Ha (elem a from)
           Hfy (f a y)]
    (have <fun> (functional f from to) :by (p/and-elim* 1 Hbij))
    (have <ser> (serial f from to) :by (p/and-elim* 2 Hbij))
    (have <bij> (bijective f from to) :by (p/and-elim* 3 Hbij))

    (have <a> _ :by ((removal-functional f from to a) <fun> y Hy Hfy))
    (have <b> _ :by ((removal-serial f from to a) <ser> (p/and-elim-left <bij>) y Hy Ha Hfy))
    (have <c> _ :by ((removal-bijective f from to a) <bij> <fun> y Hy Ha Hfy))
    (have <d> _ :by (p/and-intro* <a> <b> <c>)))

  (qed <d>))
