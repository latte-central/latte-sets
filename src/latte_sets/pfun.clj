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

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          defimplicit
                                          forall lambda
                                          assume have pose proof try-proof qed lambda]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and and* or not]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.fun :as fun]

            [latte-sets.set :as s :refer [set set-of elem seteq subset]]
            [latte-sets.quant :as sq :refer [exists-in forall-in]]
            [latte-sets.algebra :as sa]
            [latte-sets.rel :as rel :refer [rel dom ran]]
            [latte-sets.ralgebra :as ra]
            [latte-sets.powerrel :as prel :refer [rel-ex]]))

(definition functional
  "The relation `f` is functional (a.k.a. right-unique) 
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

(defthm ridentity-functional
  "The identity relation is a partial function on
any domain set."
  [T :type]
  (forall [from (set T)]
    (forall [to (set T)]
      (functional (rel/identity T) from to))))

;; TODO
(try-proof 'ridentity-functional
  (pose rid := (rel/identity T))
  (assume [from (set T) to (set T)
           x T Hx (elem x from)
           y1 T Hy1 (elem y1 to)
           y2 T Hy2 (elem y2 to)
           Hid1 (rid x y1)
           Hid2 (rid x y2)]
    (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hid1) Hid2))
  (qed <a>))


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
           x T Hx (elem x from)
           y1 U Hy1 (elem y1 to)
           y2 U Hy2 (elem y2 to)
           Hpfy1 (pf x y1)
           Hpfy2 (pf x y2)]
    (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hpfy1) Hpfy2)))
  (qed <a>))

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

(defthm image-subset-monotonous
  [[?T :type] [?U :type] [f (rel T U)] [s1 (set T)] [s2 (set T)] [sran (set U)]]
  (==> (subset s1 s2)
       (subset (image f s1 sran) (image f s2 sran))))

(proof 'image-subset-monotonous-thm
  (assume [H (subset s1 s2)]
    (assume [y U
             Hy (elem y (image f s1 sran))]
      "We have to prove y∈ f[s2]"
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
))

(comment

  ;; this needs to be updated too
  
(defthm rcomp-functional
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)]]
  (==> (functional f from)
       (functional g (image f from))
       (functional (rel/rcomp f g) from)))

(proof 'rcomp-functional-thm
  (assume [Hf _
           Hg _]
    (assume [x T
             Hx (elem x from)
             z1 V z2 V
             Hz1 ((rel/rcomp f g) x z1)
             Hz2 ((rel/rcomp f g) x z2)]
      (have <a> (exists [y1 U] (and (f x y1) (g y1 z1)))
            :by Hz1)
      (assume [y1 U
               Hy1 (and (f x y1) (g y1 z1))]
        (have <b> (exists [y2 U] (and (f x y2) (g y2 z2)))
              :by Hz2)
        (assume [y2 U
                 Hy2 (and (f x y2) (g y2 z2))]
          (have <c1> (equal y1 y2)
                :by (Hf x Hx y1 y2 (p/and-elim-left Hy1) (p/and-elim-left Hy2)))
          (have <c2> (elem y1 (image f from))
                :by ((q/ex-intro (lambda [$ T]
                                   (and (elem $ from)
                                        (f $ y1))) x) (p/and-intro Hx (p/and-elim-left Hy1))))
          (have <c3> (g y1 z2) 
                :by (eq/rewrite (p/and-elim-right Hy2) (eq/eq-sym <c1>)))

          (have <c> (equal z1 z2)
                :by (Hg y1 <c2> z1 z2 (p/and-elim-right Hy1) <c3>)))
        (have <d> _ :by (q/ex-elim <b> <c>)))
      (have <e> _ :by (q/ex-elim <a> <d>))))
  (qed <e>))

(defthm rcomp-serial
  [[?T ?U ?V :type] [f (rel T U)] [g (rel U V)] [from (set T)]]
  (==> (serial f from)
       (serial g (image f from))
       (serial (rel/rcomp f g) from)))

(proof 'rcomp-serial-thm
  (assume [Hf _
           Hg _]
    (assume [x T
             Hx (elem x from)]
      (have <a> (exists [y U] (f x y)) :by (Hf x Hx))
      (assume [y U
               Hy (f x y)]
        (have <b1> (elem y (image f from))
              :by ((q/ex-intro (lambda [z T]
                                 (and (elem z from)
                                      (f z y))) x) (p/and-intro Hx Hy)))
        (have <b> (exists [z V] (g y z))
              :by (Hg y <b1>))
        (assume [z V
                 Hz (g y z)]
          (have <c1> (and (f x y) (g y z))
                :by (p/and-intro Hy Hz))
          (have <c2> ((rel/rcomp f g) x z)
                :by ((q/ex-intro (lambda [$ U]
                                   (and (f x $) (g $ z))) y) <c1>))
          (have <c> (exists [z V]
                      ((rel/rcomp f g) x z))
                :by ((q/ex-intro (lambda [$ V]
                                   ((rel/rcomp f g) x $)) z) <c2>)))

        (have <d> (exists [z V] ((rel/rcomp f g) x z))
              :by (q/ex-elim <b> <c>)))
      (have <e> _ :by (q/ex-elim <a> <d>))))
  (qed <e>))
  
)

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
  [T :type]
  (forall [s (set T)]
    (injective (rel/identity T) s s)))

(proof 'ridentity-injective
  (pose rid := (rel/identity T))
  (assume [s (set T)
           x1 T Hx1 (elem x1 s)
           x2 T Hx2 (elem x2 s)
           y1 T Hy1 (elem y1 s)
           y2 T Hy2 (elem y2 s)
           Hr1 (rid x1 y1)
           Hr2 (rid x2 y2)
           Heqy (equal y1 y2)]
    (have <a> (equal y2 x2) :by (eq/eq-sym Hr2))
    (have <b> (equal x1 x2) :by (eq/eq-trans* Hr1 Heqy <a>)))
  (qed <b>))

(comment
  ;; this needs to be updated

(defthm rcomp-injective
  [[?T ?U ?V :type] [f1 (rel T U)] [f2 (rel U V)] [s1 (set T)] [s2 (set V)]]
  (==> (injective f1 s1 (image f1 s1))
       (injective f2 (image f1 s1) s2)
       (injective (rel/rcomp f1 f2) s1 s2)))

(proof 'rcomp-injective-thm
  (assume [Hf1 _
           Hf2 _]
    (assume [x1 T Hx1 (elem x1 s1)
             x2 T Hx2 (elem x2 s1)
             z1 V Hz1 (elem z1 s2)
             z2 V Hz2 (elem z2 s2)
             H1 ((rel/rcomp f1 f2) x1 z1)
             H2 ((rel/rcomp f1 f2) x2 z2)
             Heq (equal z1 z2)]
      "We have to prove x1=x2"
      (have <a> (exists [y1 U] (and (f1 x1 y1) (f2 y1 z1)))
            :by H1)
      (assume [y1 U
               Hy1 (and (f1 x1 y1) (f2 y1 z1))]
        (have <b> (elem y1 (image f1 s1))
              :by ((q/ex-intro (lambda [$ T]
                                 (and (elem $ s1)
                                      (f1 $ y1))) x1)
                   (p/and-intro Hx1 (p/and-elim-left Hy1))))
        (have <c> (exists [y2 U] (and (f1 x2 y2) (f2 y2 z2)))
              :by H2)
        (assume [y2 U
                 Hy2 (and (f1 x2 y2) (f2 y2 z2))]
          (have <d> (elem y2 (image f1 s1))
                :by ((q/ex-intro (lambda [$ T]
                                   (and (elem $ s1)
                                        (f1 $ y2))) x2)
                     (p/and-intro Hx2 (p/and-elim-left Hy2))))

          (have <e> (equal y1 y2)
                :by (Hf2 y1 <b> y2 <d> z1 Hz1 z2 Hz2 
                         (p/and-elim-right Hy1) (p/and-elim-right Hy2)
                         Heq))
          (have <f> (equal x1 x2)
                :by (Hf1 x1 Hx1 x2 Hx2 y1 <b> y2 <d>
                         (p/and-elim-left Hy1) (p/and-elim-left Hy2)
                         <e>)))
        (have <g> _ :by (q/ex-elim <c> <f>)))
      (have <h> _ :by (q/ex-elim <a> <g>))))

  (qed <h>))

)

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

;;; XXX : are functionality and seriality required in the definition ?
(definition smaller
  "The set `s1` is \"smaller\" than `s2`."
  [[?T ?U :type] [s1 (set T)] [s2 (set U)]]
  (rel-ex (lambda [f (rel T U)]
            (injection f s1 s2))))

(definition surjective
  "The relation `f` is surjective onto `s2` for domain `s1`."
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
  (forall-in [y s2]
    (exists-in [x s1]
      (f x y))))

;;; TODO :  if functional and serial (to check), then
;;; the   'to' set is a subset of (image f from)
;;; (or even (image f s1) ...

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
             Hfx (f x z)]
      (assume [w U Hw (elem w s2) Hfw (f x w)]
        (have <a1> (equal w z) :by (Hfun x Hx w Hw z Hz Hfw Hfx)))
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


(defthm bijection-inverse-functional
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (functional (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-functional-thm
  (pose rf := (ra/rinverse f))
  (assume [x U Hx (elem x s2)
           y1 T Hy1 (elem y1 s1)
           y2 T Hy2 (elem y2 s1)
           Hrfy1 (rf x y1)
           Hrfy2 (rf x y2)]
    (have <a1> (f y1 x) :by Hrfy1)
    (have <a2> (f y2 x) :by Hrfy2)
    (have <b> (equal y1 y2)
          :by ((bijection-injective f s1 s2 b)
               y1 Hy1
               y2 Hy2
               x Hx
               x Hx
               <a1> <a2>
               (eq/eq-refl x))))
  (qed <b>))

(defthm bijection-inverse-serial
  [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)] [b (bijection f s1 s2)]]
  (serial (ra/rinverse f) s2 s1))

(proof 'bijection-inverse-serial-thm
  (pose rf := (ra/rinverse f))
  (assume [y U Hy (elem y s2)]
    (have <a> (exists-in [x s1] (f x y))
          :by ((bijection-surjective f s1 s2 b) y Hy))
    (assume [x T Hx (elem x s1)
             Hfx (f x y)]
      (have <b1> (rf y x) :by Hfx)
      (have <b> (exists-in [x s1] (rf y x))
            :by ((sq/ex-in-intro s1 (lambda [$ T]
                                      (rf y $)) x)
                 Hx <b1>)))
    (have <c> (exists-in [x s1] (rf y x))
          :by (sq/ex-in-elim <a> <b>)))
  (qed <c>))


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
    (have <c> (equal x1 x2)
          :by (<b> y2 Hy2 x1 Hx1 x2 Hx2 <a3> <a2>)))
  (qed <c>))


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
                     
