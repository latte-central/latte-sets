(defproject latte-sets "0.2.2-SNAPSHOT"
  :description "A formalization of (typed) Set theory in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.6.1-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-sets.core
                       latte-sets.algebra
                       latte-sets.powerset
                       latte-sets.rel
                       latte-sets.ralgebra]}
  :plugins [[lein-codox "0.10.2"]])
