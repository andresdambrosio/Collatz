# Idea: inventar un problema más fuerte (inducción reforzada, Pólya)

**Estado:** cerrada para reglas finitas (ronda 11, opción C). Una conjetura chica queda abierta (C1, abajo).
**Frente:** ambos (una inducción fuerte que cierra excluye ciclos y divergencia a la vez)

## Enunciado
Buscar un enunciado `S(n)`, más fuerte que "n llega a 1", que se pruebe por inducción fuerte con una **regla finita**:
una lista de clases `r mod M` y, para cada una, un camino simbólico de largo acotado que lleva todo `n ≡ r` a algo
"menor" (donde la inducción ya vale). La inducción de descenso hacia adelante (`collatz_of_descent`, criba de Terras)
no cierra; probamos tres refuerzos:
1. **Deuda por clases** (sólo hacia adelante): `Φ(n) = log n + g(n mod 2^k)` baja en `t(r) ≤ T` pasos.
   Incluye inducción lexicográfica en (tamaño, clase) y cualquier conjunto *regular* de palabras de paridad que bajan.
2. **Familias / árbol inverso**: `S(n)` = "n está en la componente débil de 1" (Collatz ⟺ esto, porque la componente
   débil del ciclo {1,2,4} es exactamente lo que llega a 1). Inducción: todo `n` grande tiene, a distancia `≤ R` en el
   grafo **no dirigido** (pasos `T` y pasos hacia atrás `y → 2y`, `y ≡ 4 (6) → (y−1)/3`), un `m < n`. Abarca pares
   que se funden (Garner: `8k+4` y `8k+5`), `n` y `4n+1`, y predecesores.
3. **Otras medidas** (cantidad de unos, tiempo de parada, posición en el árbol inverso).

## Filtro de barreras
- **5x+1**: la versión no dirigida sí distingue algo: con 5x+1 la criba deja densidad 0,17 a módulo 8000 (3x+1: 0,03
  a módulo 2·10⁵). Pero eso no salva nada (ver abajo).
- **Positividad**: toda regla finita es un cubrimiento por cilindros de `ℤ₂ × ℤ₃` (compacidad), así que es ciega al
  signo **y a ser entero**. Una regla finita cierra ⟺ todo punto profinito tiene un camino que contrae.
- **Más allá de mod 2^k**: la versión no dirigida usa también `mod 3^k` (predecesores), o sea va más allá de mod `2^k`;
  pero sigue siendo de estados finitos, así que no va más allá de "residuos" (`mod 6^k`).
- **Específico de 3x+1**: sólo vía los pesos `log 3`, `log 2`.

## Literatura
- Terras (1976), Everett (1977): casi todo `n` baja; el tiempo de parada por coeficientes. Garner (1981): tiempo de
  parada por coeficientes = tiempo de parada salvo excepciones acotadas. **Las reglas de descenso hacia adelante son
  exactamente las palabras de paridad con `3^o < 2^t`**: no hay más reglas que las de Terras.
- Garner (1985), Burson (arXiv:2005.09456): coalescencia de trayectorias (pares que se funden), numérico.
- Andaloro (2000, Fib. Quart. 38): bastan los `n ≡ 1 (mod 16)`. Monks (2006, PAMS 134): toda progresión aritmética es
  "suficiente"; Monks et al. (2013, arXiv:1204.3904): conjuntos suficientes de densidad arbitrariamente baja. Usan el
  árbol inverso **sin** descenso (los predecesores crecen), así que no dan una inducción que cierre.
- Kontorovich–Lagarias (2009): modelos estocásticos; el árbol inverso como paseo ramificado.
- rStation collatz_32: barrera de signo (sombras de ciclos negativos) para certificados de clases forzadas.
- No encontré el refuerzo "descenso en el grafo no dirigido con regla finita" estudiado como tal (búsqueda corta; puede existir).

## Evidencia numérica
**1. Deuda hacia adelante (`scripts/ind_debt.py`).** En el grafo de clases mod `2^k`, los ciclos con peso `≥ 0` son las
palabras periódicas con `3^o > 2^L`, cuyos puntos fijos son racionales **negativos**. Hasta `L = 18` hay 70 844
palabras primitivas así; las únicas con punto entero son los ciclos de `−1`, `−5`, `−17` (y sus pares). Las sombras
`x + 2^60·m` crecen ×6·10⁸, ×15, ×5 en 50 pasos con el residuo pegado al ciclo.

**2. Criba no dirigida (`scripts/ind_undirected.py`), densidad sobreviviente.**

| módulo | sólo adelante (Terras) | no dirigida |
|---|---|---|
| `2^10·3^5 = 248 832`, R = 16 | 0,0625 | 0,0302 |
| `2^14·3^6 ≈ 1,2·10⁷`, R = 20 | 0,055 (`2^14`) | 0,0240 (meseta: igual en los tres últimos refinamientos) |
| 5x+1, `2^6·5^3 = 8000`, R = 14 | 0,31 | 0,17 |

Los `n ≡ 2 (mod 3)` impares bajan siempre por atrás (`n ← 2n ← (2n−1)/3 < n`); las sobrevivientes son `≡ 0, 1 (mod 3)`
(4617 y 2907 de 7524). La versión no dirigida saca la mitad de las clases, pero a radio fijo hay meseta.

**3. Sonda profinita (`scripts/ind_probe.py`).** `x` enorme con `x ≡ a (mod 2^400)`, `x ≡ b (mod 3^400)`; mínimo de
`z/x` en la bola no dirigida de radio `R` (sin tope efectivo: ningún nodo pasa `4^R x`). Los puntos de los ciclos
negativos **en las dos bases a la vez** bajan: `(−1,−1)`: 0,005 (R=26); `(−5,−5)`: 0,55; `(−17,−17)`: 0,94
(caminar el ciclo hacia atrás contrae ×2/3). En cambio:

| punto `(ℤ₂, ℤ₃)` | mín `z/x`, R = 24…44 |
|---|---|
| `(−1, 0)`, `(−1, 1)`, `(−5, 0)`, `(−17, 0)` | **1** (nunca baja; hasta 450 000 nodos) |
| `(−1, 2)` | 2/3 a distancia 2 |
| al azar | 0,02–0,1 |

Radio necesario para enteros concretos `n ≡ −1 (2^K)`, `n ≡ 0 (3^K)`: K = 3…9 → 11, 21, 21, 18, 23, 31, 26;
K ≥ 10 → más de 48 (y `n = 27` también necesita más de 48).

## Formalización
Nada en Lean: lo que sobrevive es una obstrucción, no un teorema hacia la conjetura. Los dos lemas de abajo son
elementales y podrían formalizarse si hiciera falta.

## Por qué falló / qué aprendimos
**Lema A (deuda hacia adelante, riguroso).** No existe ningún conjunto *regular* `P` de palabras de paridad que bajen
(`3^o < 2^t`) tal que todo `n > 1` tenga un prefijo en `P`. Tampoco una potencial `log n + g(estado)` con finitos estados.
*Prueba:* si el autómata de `P` tiene `s` estados, tras leer `1^K` (`K ≥ s`) el estado es periódico en `K` con período `p`.
Los `n = 2^{K'}m − 1` son positivos y empiezan con `1^K`, así que alguna `w` con `1^K w ∈ P` existe. Entonces
`1^{K+jp} w ∈ P` para todo `j`, con coeficiente `(3/2)^{K+jp}·c(w) → ∞`: no baja. Es la sombra del punto fijo `−1`.
Como el coeficiente depende sólo del cilindro, toda regla así también sería válida para los negativos grandes:
cumple el diagnóstico "verdadero salvo ciclos negativos ⇒ no cierra". La única familia que no es regular, las palabras
de parada por coeficientes, cubre todo ⟺ la conjetura (Terras–Garner). Inducción en "otras medidas" calculadas por
estados finitos cae acá o en la ronda 10; el tiempo de parada o la posición en el árbol inverso son la conjetura misma.

**Lema B (riguroso).** La componente débil de `−1` en el 3x+1 racional sobre `ℚ ∩ ℤ₍₂₎` está contenida en `(−∞, −1]`.
*Prueba:* si `y > −1` es impar, `3y+1 > −2`, `3y+1 ≠ −1` (pues `y = −2/3` es par) y `(3y+1)/2 > −1`; si es par,
`y/2 > −1/2`. La órbita nunca toca `{−1, −2}`.

**Obstrucción no dirigida.** En el punto profinito `x* = (−1 ∈ ℤ₂, c ∈ ℤ₃)` todo camino es un mapa afín `g`, el nodo
tiene coordenada 2-ádica `u = g(−1)` y 3-ádica `b = g(c)`, y su multiplicador real es `α = (b − u)/(c + 1)`. La
corrida `u` es un camino válido en el grafo racional (los pasos hacia adelante dependen de la paridad de `u`; el
paso `(u−1)/3` exige `u` par, y entonces `(u−1)/3` es impar), así que `u ≤ −1` por el Lema B.
- **Conjetura C1** (verificada exhaustivamente hasta R = 30 con `c ∈ {0, 1}`): `b ≥ c` en todo nodo. Entonces `α ≥ 1`:
  `x*` no baja a ningún radio y, **por compacidad, ninguna regla finita no dirigida cierra**.
- Sin C1, lo probado por cómputo exacto es: **ninguna regla no dirigida de radio ≤ 44 cierra** (la clase de `x*`
  sobrevive a todo módulo).

**Causa exacta.** Las reglas finitas ven sólo `ℤ₂ × ℤ₃` (no el signo, ni siquiera la integralidad). El obstáculo ya no
son los ciclos negativos: esos, mirados 6-ádicamente, bajan por atrás. El obstáculo es un punto **mixto** que no es racional:
- 2-ádicamente es la sombra de un ciclo negativo (`−1`, `−5`, `−17`): hacia adelante crece para siempre.
- 3-ádicamente es `0` o `1`, lo que bloquea la contracción hacia atrás: los múltiplos de 3 no tienen predecesores impares,
  y la línea `(2y−1)/3` exige `y ≡ −1 (3^s)`.

Los enteros `n ≡ −1 (2^K)`, `n ≡ 0 (3^K)` necesitan radio que crece con `K`. Reforzar el enunciado no ayuda mientras la
inducción sea local en residuos: cualquier `S` de ese tipo se puede leer en `ℤ₂ × ℤ₃`, donde es falsa o necesita tamaño.
Es la misma brecha de siempre (tamaño arquimediano vs. estructura `p`-ádica, rondas 6–10), ahora con dos primos.
