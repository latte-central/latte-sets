(defproject latte-sets "0.3.1-SNAPSHOT"
  :description "A formalization of (typed) Set theory in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.9.0-RC1"]
                 [latte "0.99.8-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-sets.core
                       latte-sets.algebra
                       latte-sets.powerset
                       latte-sets.rel
                       latte-sets.ralgebra]}
  :plugins [[lein-codox "0.10.3"]])
