---
layout: post
title: "Collatz como un juego de reescribir palabras, verificado en Lean"
date: 2026-11-24 08:00:00 -0300
ref: rewriting
tldr: "Yolcu, Aaronson y Heule convirtieron Collatz en una pregunta sobre 11 reglas que reescriben palabras cortas. Verificamos en Lean su equivalencia y sus certificados encontrados por computadora, y en el camino encontramos (y arreglamos) un pequeño hueco."
---

En 2021, Emre Yolcu, Scott Aaronson y Marijn Heule publicaron una reformulación muy linda de la conjetura
de Collatz ([arXiv:2105.14697](https://arxiv.org/abs/2105.14697)). Convierte el problema en un juego con
palabras, y es la primera reformulación que verificamos en Lean.

## Números como palabras

Escribí un número como una palabra de siete letras: dos cifras **binarias**, `f` (cero) y `t` (uno), tres
cifras **ternarias**, `0`, `1` y `2`, y dos marcadores de borde, `▷` y `◁`. La palabra se lee de izquierda a
derecha, arrancando con el valor 1 en `▷`:

- `f` duplica: $$x \mapsto 2x$$;
- `t` duplica y suma uno: $$x \mapsto 2x+1$$;
- una cifra ternaria `d` triplica y suma `d`: $$x \mapsto 3x+d$$.

Así, `▷t◁` es 3 (desde 1, duplicar y sumar uno) y `▷ft◁` es 5 (1 → 2 → 5). Al mezclar bases, un número
tiene muchas formas de escribirse; esa es la gracia.

## Once reglas

El juego tiene 11 reglas. Se puede aplicar cualquiera, en cualquier lugar de la palabra:

| Regla | Qué le hace al valor |
|---|---|
| `f◁ → ◁` | divide por 2 un número par |
| `t◁ → 2◁` | manda un impar $$2y+1$$ a $$3y+2 = \frac{3(2y+1)+1}{2}$$ |
| `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | nada: pasan una cifra binaria por encima de una ternaria |
| `▷0 → ▷t`, `▷1 → ▷ff`, `▷2 → ▷ft` | nada: reescriben en binario la primera cifra ternaria |

Las dos primeras reglas son el mapa de Collatz (acelerado): dividir por 2 si es par, $$(3n+1)/2$$ si es
impar. Las otras nueve nunca cambian el valor: solo mueven las cifras ternarias hacia la izquierda hasta que
se "disuelven" en binario al principio. Así se reescribe el 3 hasta el final:

```
▷t◁ → ▷2◁ → ▷ft◁ → ▷f2◁ → ▷1f◁ → ▷fff◁ → ▷ff◁ → ▷f◁ → ▷◁
 3     5     5      8      8      8       4      2     1
```

## El teorema

**Collatz es cierta si y solo si este juego siempre termina**, empieces por la palabra que empieces y
elijas las reglas que elijas (en el lenguaje de la reescritura: el sistema *termina*). Entre las palabras
de la forma `▷w◁`, el valor 1 (`▷◁`) es la única donde no se aplica ninguna regla; en todas las demás
siempre hay una jugada posible.

<span class="tag verified">verificado en Lean</span> Formalizamos las dos versiones:

- [`collatz_iff_terminates`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting.lean):
  Collatz ⇔ terminación sobre las palabras "canónicas" `▷w◁`;
- [`collatz_iff_terminatesAll`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting/AllWords.lean):
  Collatz ⇔ terminación sobre **todas** las palabras de las siete letras, con marcadores en cualquier lugar
  y en cualquier cantidad (el Lema 3.16 del paper). Nuestra prueba es distinta de la del paper: cortamos cada
  palabra en sus marcadores, mostramos que cada pedazo se comporta de forma independiente y cerramos los
  pedazos fáciles con argumentos de conteo simples.

## ¿Para qué? Certificados

La terminación de un sistema de reescritura es algo que a veces las computadoras pueden *demostrar*,
encontrando un "certificado": una forma de asignarles matrices a las letras de modo que cada regla haga
bajar cierta cantidad. Por eso esta reformulación entusiasma: convierte Collatz en el tipo de problema que
atacan las herramientas automáticas.

Yolcu, Aaronson y Heule encontraron certificados así para cada **subsistema** que se obtiene borrando una de
las 11 reglas (cada uno de esos termina) y para una variante de Farkas. Hasta donde pudimos encontrar, sus
certificados nunca se habían verificado en un asistente de pruebas. (Algunos de sus sistemas están en la
base de problemas de la competencia internacional de terminación, cuya categoría certificada usa CeTA, un
verificador probado en Isabelle. No revisamos si alguna herramienta los certificó ahí.)

<span class="tag verified">verificado en Lean</span> Escribimos en Lean un verificador de interpretaciones
matriciales naturales y árticas, y volvimos a chequearlos todos
([`SRS.termIn_without`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting/Subsystems.lean),
[`SRS.Farkas.farkas_convergent`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting/Farkas.lean)).
Al hacerlo encontramos un pequeño hueco en el argumento de Farkas del paper (§4.2). El paper dice que
"repeatedly performing the rightmost possible rewrite" (aplicar una y otra vez la reescritura posible más a
la derecha) simula la trayectoria, pero esa estrategia se traba en tres palabras cortas (`▷t◁`, `▷f◁` y
`▷ft◁`). La conclusión sigue valiendo; Lean necesitó un invariante extra y un chequeo finito para llegar.

## La trampa

Sacar una regla vuelve el problema mucho más fácil. El premio de verdad es un certificado para el sistema
**completo**, y eso sería una prueba de Collatz. <span class="tag lit">literatura</span> En un preprint de
2026, formalizado en Lean, Hiroyuki Nashida mostró que las técnicas de matrices que funcionaron para los
subsistemas (interpretaciones matriciales naturales y árticas, usadas solas) **nunca** pueden sacar ni una
regla del sistema completo, en ninguna dimensión. Agregamos un filtro propio chiquito: si cambiás la regla
`t◁ → 2◁` por `t◁ → 1◁`, el juego simula $$3x-1$$, que tiene ciclos.
<span class="tag verified">verificado en Lean</span> En ese sistema "vecino" no se puede sacar ninguna regla
([`SRS.Neighbor.not_relSN_d1`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting/Neighbors.lean)).
Así que cualquier certificado para Collatz tiene que ver la diferencia entre la cifra 2 y la cifra 1 en esa
única regla.

Los próximos posts explican por qué todos los intentos en esta dirección (incluidos los nuestros) se frenan
donde se frenan.

## Referencias

- E. Yolcu, S. Aaronson, M. J. H. Heule, "An Automated Approach to the Collatz Conjecture",
  *Journal of Automated Reasoning* 67 (2023), n.º 2.
  [doi:10.1007/s10817-022-09658-8](https://doi.org/10.1007/s10817-022-09658-8),
  [arXiv:2105.14697](https://arxiv.org/abs/2105.14697). Certificados:
  [github.com/emreyolcu/rewriting-collatz](https://github.com/emreyolcu/rewriting-collatz).
- H. M. Farkas, "Variants of the 3N+1 conjecture and multiplicative semigroups", en *Geometry, Spectral
  Theory, Groups, and Dynamics*, Contemporary Mathematics 387 (2005), 121–127.
  [doi:10.1090/conm/387/07238](https://doi.org/10.1090/conm/387/07238)
- H. Nashida, "Natural-number and arctic matrix interpretations alone make no progress, in any dimension,
  on the Collatz rewriting system", preprint (2026).
  [doi:10.5281/zenodo.23147025](https://doi.org/10.5281/zenodo.23147025), código Lean:
  [github.com/harappa/collatz-arctic-interpretation-barriers](https://github.com/harappa/collatz-arctic-interpretation-barriers)
