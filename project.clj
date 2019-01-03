(defproject latte-sets "1.0b2-SNAPSHOT"
  :description "A formalization of (typed) Set theory in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.0"]
                 [latte-prelude "1.0b2-SNAPSHOT"]]
  :main latte-sets.main
  :aliases {"certify" ["run" ":certify"]
            "clear-cert" ["run" ":clear-cert"]}
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-sets.core
                       latte-sets.algebra
                       latte-sets.powerset
                       latte-sets.rel
                       latte-sets.ralgebra
                       latte-sets.pfun]}
  :plugins [[lein-codox "0.10.5"]])

