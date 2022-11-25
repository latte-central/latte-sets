(defproject latte-sets "1.0b10-SNAPSHOT"
  :description "A formalization of (typed) Set theory in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [latte-prelude "1.0b10-SNAPSHOT"]]
  :main latte-sets.main
  :aliases {"certify" ["run" ":certify"]
            "clear-cert" ["run" ":clear-cert"]}
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-sets.set
                       latte-sets.quant
                       latte-sets.algebra
                       latte-sets.powerset
                       latte-sets.rel
                       latte-sets.ralgebra
                       latte-sets.equiv
                       latte-sets.powerrel
                       latte-sets.pfun]}
  :profiles {:uberjar {:aot [latte-sets.main]}}
  :plugins [[lein-codox "0.10.8"]])


