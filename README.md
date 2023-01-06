### Version incrémentale de EvalMaxSAT

Version incrémentale de EvalMaxSAT tel que présenté en 889B. 

Basée sur l'interface IPAMIR : https://bitbucket.org/coreo-group/ipamir/src/master/


### Benchmarks

Avant avoir ajouté les fonctionnalités décrites, la version incrémentale du solveur solvait 284 benchmarks (141 timeout) sur un total de 103 861 secondes.

Après avoir ajouté les fonctionnalités, la version incrémentale en résout 317 (108 timeout) sur un total de 87 828 secondes.

Cela représente donc 37 benchmarks de plus résolus.

Il faut toutefois noter que pour la nouvelle version incrémentale, la méthode `adapt_exact` a été désactivée à cause de bogues. Quand ces bogues seront résolus et la méthode réactivée, la nouvelle version solvera encore plus de benchmarks.

Les benchmarks réalisés (complete, unweighted, 2021, MaxSATEvaluations) ont été réalisé à partir de `main.cpp`. Cette 'application' a comme but d'être polyvalente et teste toutes les méthodes de l'interface ipamir (assume, add_soft_lit, add_hard, etc). L'écart entre la nouvelle version incrémentale et l'ancienne variera selon l'application utilisée.
