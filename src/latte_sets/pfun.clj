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

            [latte-sets.set :as s :refer [set set-of elem seteq]]
            [latte-sets.quant :as sq :refer [exists-in forall-in]]
            [latte-sets.algebra :as sa]
            [latte-sets.rel :as rel :refer [rel dom ran]]
            [latte-sets.powerrel :as prel :refer [rel-ex]]))

(definition functional
  "The relation `f` is functional (a.k.a. right-unique) on the domain-set `from`.
 Note that the relation `f`  outside `from` is not consrained."
  [[?T ?U :type], f (rel T U), from (set T)]
  (forall-in [x from]
    (forall [y1 y2 U]
      (==> (f x y1)
           (f x y2)
           (equal y1 y2)))))

(defn fetch-functional-type [def-env ctx t]
  (latte.utils/decomposer
   (fn [t]
     (if (clojure.core/and (seq? t)
                           (= (count t) 4)
                           (= (first t) #'latte-sets.pfun/functional-def))
       (into [] (rest t))
       (throw (ex-info "Not a functional type." {:type t}))))
   def-env ctx t))

(defthm ridentity-functional
  "The identity relation is a partial function on
any domain set."
  [T :type]
  (forall [from (set T)]
    (functional (rel/identity T) from)))

(proof 'ridentity-functional
  (pose rid := (rel/identity T))
  (assume [from (set T)
           x T Hx (elem x from)
           y1 T y2 T
           Hid1 (rid x y1)
           Hid2 (rid x y2)]
    (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hid1) Hid2)))
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
    (functional (functional-fun f) from)))

(proof 'functional-fun-prop-thm
  (pose pf := (functional-fun f))
  (assume [from (set T)
           x T Hx (elem x from)
           y1 U y2 U
           Hy1 (pf x y1)
           Hy2 (pf x y2)]
    (have <a> (equal y1 y2) :by (eq/eq-trans (eq/eq-sym Hy1) Hy2)))
  (qed <a>))

(definition domain
  "The actual domain of relation `f`, taking antecedents in `from`.
It is sometimes called the active domain of `f`."
  [[?T ?U :type], f (rel T U), from (set T)]
  (set-of [x T] (and (elem x from)
                     (exists [y U] (f x y)))))

(definition image
  "The image of set `from` through relation `f`. This is also
sometimes called the *range* or *codomain* but image is less ambiguous
(especially in type theory)."
  [[?T ?U :type], f (rel T U), from (set T)]
  (set-of [y U] (exists-in [x from] (f x y))))

(definition serial
  "The relation `f` covers all of (is total wrt.) the provided `from` domain set."
  [[?T ?U :type], f (rel T U), from (set T)]
  (forall-in [x from]
    (exists [y U]
      (f x y))))

(definition serial-alt
  "Alternative definition for [[serial]]."
  [[?T ?U :type], f (rel T U), from (set T)]
  (seteq (domain f from) from))

(defthm serial-serial-alt
  [[?T ?U :type], f (rel T U), from (set T)]
  (==> (serial f from)
       (serial-alt f from)))

(proof 'serial-serial-alt-thm
  (assume [Htot (serial f from)]
    "First the subset direction."
    (assume [x T Hx (elem x (domain f from))]
      "We have to prove that `x` is in `from`."
      (have <a> (elem x from) :by (p/and-elim-left Hx)))
    "Second the superset direction."
    (assume [x T Hx (elem x from)]
      "We have to prove that `x` is in `(domain f from)`"
      (have <b1> (exists [y U] (f x y)) :by (Htot x Hx))
      (have <b> (elem x (domain f from)) :by (p/and-intro Hx <b1>)))
    "Deduce set-equality."
    (have <c> (seteq (domain f from) from) :by (p/and-intro <a> <b>)))
  (qed <c>))
      
(defthm serial-alt-serial
  [[?T ?U :type], f (rel T U), from (set T)]
  (==> (serial-alt f from)
       (serial f from)))

(proof 'serial-alt-serial-thm
  (assume [Htot (serial-alt f from)]
    (assume [x T Hx (elem x from)]
      (have <a> (elem x (domain f from)) 
            :by ((p/and-elim-right Htot) x Hx))
      (have <b> (exists [y U] (f x y))
            :by (p/and-elim-right <a>))))
  (qed <b>))

(defthm functional-fun-serial
  "A type-theoretic function `f` is always serial."
  [[?T ?U :type], f (==> T U)]
  (forall [from (set T)]
    (serial (functional-fun f) from)))

(proof 'functional-fun-serial-thm
  (pose rf := (functional-fun f))
  (assume [from (set T)]
    "subset (if) part"
    (assume [x T
             Hx (elem x (domain rf from))]
      (have <a> (elem x from) :by (p/and-elim-left Hx)))
    "cosubset (only if) part"
    (assume [x T
             Hx (elem x from)]
      (have <b1> (rf x (f x)) :by (eq/eq-refl (f x)))
      (have <b2> (exists [y U] (rf x y))
            :by ((q/ex-intro (lambda [y U] (rf x y)) (f x)) <b1>))
      (have <b> (elem x (domain rf from)) :by (p/and-intro Hx <b2>)))
    "(sub)set equality"
    (have <c> (seteq (domain rf from) from) :by (p/and-intro <a> <b>))
    (have <d> (serial-alt rf from) :by <c>)
    (have <e> (serial rf from) :by ((serial-alt-serial rf from) <d>)))
  (qed <e>))

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

(defthm rcomp-injective
  [[?T ?U ?V :type] [f1 (rel T U)] [f2 (rel U V)] [s1 (set T)] [s2 (set V)]]
  (==> (injective f1 s1 (image f1 s1))
       (injective f2 (image f1 s1) s2)
       (injective (rel/rcomp f1 f2) s1 s2)))

(try-proof 'rcomp-injective-thm
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

(comment
  ;; TODO

(defthm compose-pinjective
  [[?T ?U ?V :type] [f (rel U V)] [ffrom (set U)] [fto (set V)] [g (rel T U)] [gfrom (set T)] [gto (set U)]]
  (==> (pinjective f ffrom fto)
       (pinjective g gfrom gto)
       (pinjective (compose f ffrom g gfrom) gfrom fto)))

(proof 'compose-pinjective-thm
  (pose h := (compose f ffrom g gfrom))
  (assume [Hf (pinjective f ffrom fto)
           Hg (pinjective g gfrom gto)
           x1 T Hx1 (elem x1 gfrom)
           x2 T Hx2 (elem x2 gfrom)
           y1 V Hy1 (elem y1 fto)
           y2 V Hy2 (elem y2 fto)
           Hh1 (h x1 y1)
           Hh2 (h x2 y2)
           Heq (equal y1 y2)]
    (have <a> (exists-in [z1 ffrom] (and (g x1 z1) (f z1 y1)))
          :by (Hh1 Hx1))
    (assume [z1 U Hz1 (elem z1 ffrom)
             Hex1 (and (g x1 z1) (f z1 y1))]
      (have <b> (exists-in [z2 ffrom] (and (g x2 z2) (f z2 y2)))
            :by (Hh2 Hx2))
      (assume [z2 U Hz2 (elem z2 ffrom)
               Hex2 (and (g x2 z2) (f z2 y2))]
        (have <c1> (equal z1 z2) 
              :by (Hf z1 Hz1 z2 Hz2 y1 y2
                      (p/and-elim-right Hex1)
                      (p/and-elim-right Hex2)
                      Heq))
        (have <c> (equal x1 x2)
              :by (Hg x1 Hx1 x2 Hx2 z1 z2
                      (p/and-elim-left Hex1)
                      (p/and-elim-left Hex2)
                      <c1>)))
      (have <d> _ 
            :by ((sq/ex-in-elim ffrom (lambda [z2 U] (and (g x2 z2) (f z2 y2)))
                                (equal x1 x2)) <b> <c>)))
    (have <e> _
          :by ((sq/ex-in-elim ffrom (lambda [z1 U] (and (g x1 z1) (f z1 y1)))
                              (equal x1 x2)) <a> <d>)))
  (qed <e>))
)

(definition psmaller
  "The set `s1` is \"smaller\" than `s2`."
  [[?T :type] [s1 (set T)] [s2 (set T)]]
  (rel-ex (lambda [f (rel T T)]
            (and* (functional f s1)
                  (serial f s1)
                  (pinjective f s1 s2)))))

(definition psurjective
  "A surjective partial relation/function."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [y to]
    (exists-in [x from]
      (f x y))))

(definition pbijective
  "A bijective partial relation/function."
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (and (pinjective f from to)
       (psurjective f from to)))

(defthm pinjective-single
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (serial f from) ;; totality is needed, although not functionality
       (pinjective f from to)
       (forall-in [z to]
         (sq/single-in from (lambda [x T] (forall [w U] 
                                            (==> (f x w)
                                                 (equal w z))))))))

(proof 'pinjective-single-thm
  (assume [Htot _
           Hinj _
           z U Hz (elem z to)]
    (pose P := (lambda [x T] (forall [w U]
                               (==> (f x w)
                                    (equal w z)))))
    (assume [x T Hx (elem x from)
             y T Hy (elem y from)
             HPx (P x)
             HPy (P y)]
      "We have to show that x equals y"
      (assume [xim U
               Hxim (f x xim)]
        (have <a1> (equal xim z) :by (HPx xim Hxim))
        (have <a2> (f x z) :by (eq/rewrite Hxim <a1>)))
      (have <a> (f x z) :by (q/ex-elim (Htot x Hx) <a2>))
      (assume [yim U
               Hyim (f y yim)]
        (have <b1> (equal yim z) :by (HPy yim Hyim))
        (have <b2> (f y z) :by (eq/rewrite Hyim <b1>)))
      (have <b> (f y z) :by (q/ex-elim (Htot y Hy) <b2>))
      (have <c> (equal x y) :by (Hinj x Hx y Hy z Hz z Hz <a> <b> (eq/eq-refl z))))
    (have <d> _ :by ((sq/single-in-intro from P) <c>)))
  (qed <d>))


(defthm pbijective-unique
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (==> (functional f from)
       (serial f from)
       (pbijective f from to)
       (forall-in [z to]
         (sq/unique-in from (lambda [x T] (forall [w U] 
                                            (==> (f x w)
                                                 (equal w z))))))))

(proof 'pbijective-unique-thm
  (assume [Hfun _
           Htot _
           Hbij _
           z U Hz (elem z to)]
    (have Hinj (pinjective f from to) :by (p/and-elim-left Hbij))
    (have Hsurj (psurjective f from to) :by (p/and-elim-right Hbij))
    (pose P := (lambda [x T] (forall [w U]
                               (==> (f x w)
                                    (equal w z)))))
    "First we have to show  that there's an `x` in `s` such as `(P x)`"
    "We exploit surjectivity."
    (assume [x T Hx (elem x from)
             Hfx (f x z)]
      (assume [w U Hw (f x w)]
        (have <a1> (equal w z) :by (Hfun x Hx w z Hw Hfx)))
      (have <a2> (P x) :by <a1>)
      (have <a3> (exists-in [x from] (P x)) :by ((sq/ex-in-intro from P x) Hx <a2>)))
    (have <a4> (exists-in [x from] (f x z)) :by (Hsurj z Hz))
    ;; XXX : this does not work if <a4> is inlined within the elimination below
    (have <a> (exists-in [x from] (P x)) :by (sq/ex-in-elim <a4> <a3>))
    "The second part is thanks to injectivity."
    (have <b> _ :by ((pinjective-single f from to) Htot Hinj z Hz))
    "The uniqueness follows"
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))
      
      
