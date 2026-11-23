---
layout: page
title: Las reglas de este proyecto
permalink: /es/reglas/
ref: rules
---

Este es mi proyecto ([Andrés D'Ambrosio](https://x.com/andresdambrosio)). El objetivo es demostrar la
conjetura de Collatz y compartir todo en el camino. La conjetura atrae muchas "demostraciones"; este
proyecto quiere ser lo contrario: lento, verificable y honesto sobre lo que logró y lo que no. Estas son
las reglas.

## 1. Lean es el juez

Un resultado cuenta solo cuando lo acepta el asistente de pruebas [Lean](https://lean-lang.org).
En concreto: todo el proyecto compila con `lake build`, y `#print axioms` del teorema muestra solo los tres
axiomas estándar de Lean (`propext`, `Classical.choice`, `Quot.sound`). Nada de `sorry`, ni axiomas nuevos,
ni hipótesis escondidas. Cualquiera puede repetir el chequeo: es un comando en el
[repositorio](https://github.com/andresdambrosio/Collatz).

## 2. Cada afirmación lleva una etiqueta

- <span class="tag verified">verificado en Lean</span>: lo chequeó el kernel de Lean en el repositorio,
  con el nombre del teorema.
- <span class="tag lit">literatura</span>: demostrado en un artículo publicado o un preprint, todavía no
  chequeado acá. Digo quién lo demostró.
- <span class="tag heur">heurística</span>: un argumento de plausibilidad, un cálculo o un modelo
  probabilístico. Útil, pero no es una demostración.
- <span class="tag open">abierto</span>: nadie lo sabe.

## 3. Los fracasos se publican

La mayoría de las ideas fallan. Cuando una falla, escribo exactamente por qué, en la carpeta
[`Ideas/`](https://github.com/andresdambrosio/Collatz/tree/main/Ideas) y acá. Un fracaso preciso es
información; un éxito vago es ruido.

## 4. Primero el crédito y la literatura

Antes de decir que algo es nuevo, busco en la literatura y cuento lo que encontré. Mucho de lo que está
verificado en el repositorio es un *chequeo formal de matemática publicada*, y las entradas lo dicen.

## 5. Cómo se trabaja

Trabajo con un asistente de IA (Claude, de Anthropic), que escribe buena parte del código Lean y del
análisis. Yo marco la dirección y decido qué se publica. Justamente por eso existe la regla 1: a Lean no le
importa quién escribió una demostración.

## 6. La conjetura está abierta hasta que Lean diga lo contrario

Mientras `collatz_conjecture` en
[`Collatz/Main.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Main.lean) no compile
sin `sorry` y no pase la regla 1, la conjetura de Collatz está abierta, acá como en todas partes.

## 7. Cualquiera puede contribuir

El repositorio es abierto (Apache-2.0). Ideas, correcciones y demostraciones en Lean son bienvenidas; ver
[CONTRIBUTING.md](https://github.com/andresdambrosio/Collatz/blob/main/CONTRIBUTING.md) (en inglés).
