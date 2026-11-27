# Collatz en Lean

### Un curso que recorre, paso a paso y con demostraciones verificadas en Lean, todo lo que sabemos (y lo que no) sobre la conjetura de Collatz

**Andrés D'Ambrosio**

> **Advertencia, la más importante del libro.** La conjetura de Collatz es un **problema abierto**. Este libro
> no la demuestra. Lo que cuenta son reformulaciones verificadas, cotas, barreras (pruebas de que ciertos
> caminos no pueden funcionar) y lecturas críticas de trabajos ajenos.

## Autoría y créditos

La conjetura es de **Lothar Collatz** (1937). Los resultados que recorremos son, en su gran mayoría, de otras
personas: Terras, Eliahou, Conway, Kurtz y Simon, Yolcu, Aaronson y Heule, Tao, Applegate y Lagarias, y varios
más. Los citamos en cada capítulo.

El libro y la formalización en Lean son de **Andrés D'Ambrosio** (o sea, yo), escritos con ayuda intensiva de IA
(ver el [prefacio](00-prefacio.md)). En cada capítulo hay una sección **"Qué es nuestro y qué no"** que dice
exactamente qué aporta el proyecto. Casi siempre es la *verificación formal* de algo que ya existía en papel, y
lo decimos así. Si ven un error o un crédito mal dado, avísenme en el
[repositorio](https://github.com/andresdambrosio/Collatz/issues) y lo corrijo enseguida.

Este libro acompaña al repositorio [github.com/andresdambrosio/Collatz](https://github.com/andresdambrosio/Collatz).
Cada capítulo explica la matemática y el código Lean de un tramo del proyecto.

## Etiquetas

Cada afirmación importante lleva una etiqueta que dice qué tan firme es:

- **[Lean]**: está demostrado y lo chequeó Lean en este repositorio, con los axiomas estándar. Es lo más firme
  que hay.
- **[Literatura]**: lo demostró otra persona y está publicado, pero no lo verificamos nosotros.
- **[Experimento]**: lo vimos en cálculos con computadora. No es una demostración.
- **[Abierto]**: nadie sabe.

## Índice

**Parte I: Punto de partida**

0. [Prefacio: qué es este libro y cómo leerlo](00-prefacio.md)
1. [El problema](01-el-problema.md)
2. [Lean, en lo mínimo indispensable](02-lean.md)

**Parte II: Las primeras demostraciones**

3. [Definiciones y primeros teoremas](03-primeros-teoremas.md)
4. [Dos maneras de fallar: ciclos o divergencia](04-ciclos-o-divergencia.md)
5. [Los ciclos tienen que ser larguísimos: 15 601](05-ciclos-largos.md)

**Parte III: Reformulaciones**

6. [Collatz como un juego de palabras](06-reescritura.md)
7. [Certificados de terminación](07-certificados.md)
8. [Clases forzadas](08-clases-forzadas.md)
9. [Collatz ⟺ casi todos llegan a 1](09-casi-todos.md)

**Parte IV: Límites**

10. [No hay un método general: Conway y Kurtz–Simon](10-indecidibilidad.md)
11. [Leer pruebas ajenas: Opfer y la Conjetura A](11-pruebas-ajenas.md)
12. [Barreras: por qué fallan los métodos locales](12-barreras.md)

**Parte V: La frontera**

13. [Problemas abiertos](13-problemas-abiertos.md)

[Bibliografía](99-bibliografia.md)

## Convenciones

- Los nombres de declaraciones Lean aparecen en `monoespaciado`, por ejemplo `collatz_iff`. Se pueden buscar
  directamente en el código.
- $\mathbb{N} = \{0, 1, 2, \dots\}$. "Número" quiere decir entero positivo, salvo que se diga otra cosa.
- Hay **dos** versiones del mapa, y conviene no confundirlas: la **clásica** ($n/2$ o $3n+1$) y la **acelerada**
  ($n/2$ o $(3n+1)/2$). En el código, `T` (sin prefijo) es la clásica y `Collatz.T` es la acelerada. El capítulo 4
  explica por qué da igual cuál se use.
