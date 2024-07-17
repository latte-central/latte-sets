(ns latte-sets.main
  (:gen-class)
  
  (:require [latte.main :refer [latte-main]]))

(defn -main [& args]
  (latte-main args "latte-sets" '[latte-sets.set latte-sets.quant latte-sets.powerset latte-sets.algebra
                                  latte-sets.rel latte-sets.ralgebra latte-sets.powerrel latte-sets.equiv
                                  latte-sets.pfun latte-sets.compare]))



