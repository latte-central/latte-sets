(ns latte-sets.main
  (:gen-class)
  (:require [latte.main :refer [latte-main]]
            [latte-sets.core]
            [latte-sets.quant]
            [latte-sets.powerset]
            [latte-sets.algebra]
            [latte-sets.rel]
            [latte-sets.ralgebra]
            [latte-sets.powerrel]
            [latte-sets.pfun]))


(defn -main [& args]
  (latte-main args "latte-sets" '[latte-sets.core latte-sets.quant latte-sets.powerset latte-sets.algebra
                                  latte-sets.rel latte-sets.ralgebra latte-sets.powerrel
                                  latte-sets.pfun]))


(-main ":certify")



