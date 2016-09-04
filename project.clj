(defproject latte-sets "0.0.5-SNAPSHOT"
  :description "A formalization of (typed) Set theory in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.3.2-SNAPSHOT"]]
  :codox {:metadata {:doc/format :markdown}
          :namespaces [latte-sets.core]}
  :plugins [[lein-codox "0.9.5"]])
