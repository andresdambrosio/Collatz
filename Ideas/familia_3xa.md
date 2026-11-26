# Idea: toda la familia 3x+a a la vez (ciclos racionales de 3x+1)

**Estado:** refutada como vía (cerrada); queda un catálogo verificado y una medición del modelo aleatorio
**Frente:** ciclos

## Enunciado
Para `a > 0` impar con `gcd(a, 6) = 1`, sea `f_a(x) = (3x + a)/2^{v₂(3x+a)}` sobre los impares positivos. Un ciclo con
`k` impares y `ℓ` divisiones por 2 cumple (Böhm–Sontacchi)

    x · (2^ℓ − 3^k) = a · A_P,     A_P = Σ_{i<k} 3^{k−1−i} 2^{s_i}   (s_0 = 0 < s_1 < … : posiciones de los impares).

Un ciclo es **primitivo** si `gcd(x, a) = 1`; los demás son `q·(ciclo primitivo de f_{a/q})` ("forzados"). Los primitivos de
`f_a` son exactamente los **ciclos racionales `x/a` de 3x+1 con denominador `a`** (Lagarias 1990). Cada palabra cíclica
aperiódica `P` con `B = 2^ℓ − 3^k > 0` da *un* ciclo racional, con denominador

    d_P = B / gcd(A_P, B)          (siempre d_P | B).

O sea: **la familia entera es una partición de los ciclos racionales positivos de 3x+1 según su denominador**, y la parte
de ciclos de Collatz es la pregunta "¿la celda `d = 1` contiene sólo al ciclo trivial `(k, ℓ) = (1, 2)`?", es decir,
"`B ∤ A_P` para toda `P ≠ (1,2)`" (Belaga–Mignotte 2006, Teo. 5(7)).

La idea "fuera de la caja": buscar un enunciado **uniforme en `a`** (conteo, suma, identidad, cota sumada sobre `a`) que sea
demostrable y que, especializado o despejado, diga algo **puntual** de `a = 1`.

## Filtro de barreras
- **¿Falla para 5n+1?** No aplica directamente (es una afirmación sobre ciclos). El filtro relevante es el de la tarea:
  ¿distingue `a = 1` de `a = 5, 7, 13, …`, que sí tienen ciclos primitivos no triviales? Ver "Filtro a = 5" abajo: **no**.
- **¿Usa n > 0?** Sí: `B > 0` y la positividad del mínimo del ciclo entran en el modelo (`A_min ≥ B/d`).
- **¿Va más allá de mod 2^k?** Sí: es divisibilidad por `2^ℓ − 3^k`, no 2-ádica. (2-ádicamente la familia es trivial:
  todo punto periódico del shift es un racional con denominador impar, y todos son ciclos de algún `f_a`.)
- **¿Va más allá de "casi todos"?** Ése es el punto, y es donde muere: lo uniforme en `a` es, en el mejor caso,
  "para casi todo `a`" o "en promedio sobre `a ≤ X`", y `a = 1` pesa `1/X`.
- **¿Usa algo específico de 3n+1?** La estructura (partición por denominadores) vale igual para `px + q`.

## Literatura
Leído directamente (PDF/texto):
- **Belaga–Mignotte 2006**, *Walking cautiously into the Collatz wilderness*, DMTCS proc. AG, 249–260 (leído completo).
  - Conjetura 2 (atribuida a Lagarias 1990): todo `f_d` tiene **al menos un** ciclo primitivo, y **finitos**.
  - Conjetura 3 (dual): para todo `n`, hay infinitos `d` con un ciclo primitivo de `f_d` que pasa por `n`.
  - Tabla (en su preprint 2006-15): `1 ≤ d ≤ 19999`, 6667 sistemas, **42765 ciclos primitivos**; `ω(d) = 1` en 1481 sistemas,
    `2` en 1507, `3` en 1005; máximo `ω(14303) = 944`; lista de los once `d` con `ω > 160`. Advierten que la completitud
    no está garantizada.
  - Teo. 5: "corona de Collatz" `A_{k,ℓ}` (los valores de `A_P`), su cardinal es el conteo de collares (fórmula con Möbius),
    cotas `3^k − 2^k ≤ A ≤ 2^{ℓ−k+1}3^{k−1} − …`, y la reformulación: Collatz-ciclos ⟺ `B_{k,ℓ}` no divide a ningún
    miembro de su corona; Conj. de Lagarias ⟺ `d = B/gcd(B, A)` se realiza para todo `d`, finitas veces.
  - Su comentario final: la versión dual (`A | B`) tiene infinitos candidatos por la inclusión `A_{k,ℓ} ⊂ A_{k,ℓ+j}`;
    la de Collatz (`B | A`) tiene finitos por cada `(k, ℓ)`. **No hay simetría que intercambie los papeles.**
- **Kaneda 2015**, *Two remarks on the Collatz cycle conjecture*, Fibonacci Quart. 53(2) (leído): prueba corta de la cota
  de Belaga: perigeo `a_min ≤ |d|·k·3^k` (elemental) y `a_min < |d|·k^C` (Baker; "debido a Lagarias" en nota al pie).
  Conjetura "(3x+d)-cycle": para cada `d ≡ ±1 (mod 6)` hay finitos ciclos.
- **Bibliografías anotadas de Lagarias** (arXiv math/0309224 y math/0608208, leídas las entradas pertinentes).

Sólo a través de las bibliografías anotadas (no pude leer el original; no invento su contenido):
- **Lagarias 1990**, *The set of rational cycles for the 3x+1 problem*, Acta Arith. 56, 33–53. Según la reseña:
  estudia los ciclos de `T_k` con `gcd(x, k) = 1` (= ciclos racionales `x/k`), **conjetura que todo `T_k` tiene uno**,
  prueba que **infinitos `k` tienen ≥ `k^{1−ε}`** ciclos de período `≤ log k`, que **infinitos `k` no tienen ninguno** de
  período `< k^{1/3}`, y da estimaciones del conteo `C(k, y)` (ciclos de período `≤ y`) **para todos los `k ≤ x`** (en
  promedio), por ejemplo `C(k, 1,01k) ≤ 5k(log k)^5`. Todos son enunciados existenciales ("infinitos `k`") o promediados.
- **Belaga–Mignotte 1998/99**, Exp. Math. 7: a lo sumo `d·k^c` órbitas periódicas con ≤ `k` impares, `c` efectiva
  (Baker–Wüstholz).
- **Belaga 2003**, Acta Arith. 106: `prg(C) ≤ d/(2^{ℓ/k} − 3)`, de donde `log₂3 < ℓ/k ≤ log₂(d+3)`; número de ciclos de
  largo impar `k` ≤ `d·k^{c₀}` con `c₀ = 32`.
- **Halbeisen–Hungerbühler 1997**, Acta Arith. 78: cotas "óptimas" para el mínimo de un ciclo racional de largo `k`
  (usadas para cotas de largo de ciclos enteros; no para la familia).
- **Brent 2002** (arXiv math/0204170, sólo el resumen): experimentos; `k = 7, 19, 31` tendrían un solo ciclo primitivo.
- **Simons 2008** (Acta Arith. 131) y Simons–de Weger 2004: criterios de no existencia de `m`-ciclos para `3x + q`
  (que *sí* tiene `m`-ciclos para `m` chico); el invariante `S(q)` (suma de largos de ciclos) "no se sabe finito para
  ningún `q`".
- **Wirsching**: lo que encontré de él (LNM 1681, densidad de predecesores) no trata la familia 3x+a; no hallé un trabajo
  suyo sobre ciclos racionales. Lo dejo dicho, sin inventar.
- Aliyev 2023 (arXiv:2307.11990, leído el inicio): combinaciones lineales enteras de términos de ciclos racionales; sin conteos.

**Resumen de la literatura:** los únicos enunciados **demostrados y uniformes en `a`** son cotas polinomiales
(perigeo `≤ a·k^C`, número de ciclos de largo impar `k` `≤ a·k^{32}`), vía Baker, y resultados de Lagarias para
**infinitos** o **casi todos** los denominadores. Ninguno da cero para `a = 1`. La finitud para cada `a` está abierta
(incluido `a = 1`).

## Evidencia numérica
Scripts: `scripts/fam_cycles.py` (búsqueda por mínimo, numpy), `scripts/fam_necklaces.py` (todos los ciclos racionales
de largo `ℓ ≤ L` y estadística de `A_P` módulo los divisores de `B`), `scripts/fam_analysis.py`, `scripts/fam_model.py`.

**1. Catálogo `d < 20000` (verificado numéricamente, reproduce a Belaga–Mignotte).**
`python3 scripts/fam_cycles.py 19999 256 c.tsv 1000000` (mínimos `≤ max(256d, 10⁶)`, 159 s, < 1 GB):
- 6667 sistemas, **42645 primitivos** (BM: 42765; faltan 120, todos con `ℓ > 24` y mínimo `> 256d`, ver abajo y punto 2).
- `ω(d) = 0, 1, 2, 3`: **0, 1481, 1507, 1004** (BM: –, 1481, 1507, 1005). **Ningún `d < 20000` sin ciclo primitivo**
  (Conj. de Lagarias, confirmada en el rango, como en BM).
- Los once `d` con más ciclos coinciden con la tabla de BM (944 en 14303, 534 en 6487, 335 en 13085, 329 en 14197, …).
- Con mínimos `≤ max(1024d, 10⁶)` (538 s, 0,56 GB): **42757 primitivos** (faltan 8 respecto de BM; los 112 nuevos tienen
  `x_min/d ∈ (256, 1024]` y aparece `ω(17021) = 258`, como en BM). `ω = 3` sigue en 1004: hay al menos un `d` con un ciclo
  de mínimo `> 1024d`. Ningún ciclo "sin decidir".
- Control: en todo ciclo primitivo `d | 2^ℓ − 3^k` (0 fallas), la ecuación del ciclo vale (assert), y la cota de Belaga
  `x_min ≤ d/(2^{ℓ/k} − 3)` y `log₂3 < ℓ/k ≤ log₂(d+3)` no se violan nunca (sobre los 42757; la cota se alcanza con igualdad en los ciclos `k = 1`, `d = 2^ℓ − 3`, `x = 1`).

**2. Completitud por largos.** `fam_necklaces.py 24 19999`: todos los ciclos racionales con `ℓ ≤ 24` (vectores
aperiódicos, 13,6 s, 1,1 GB). Los 6652 ciclos con `ℓ ≤ 24` y `d < 20000` coinciden **exactamente** con los de la búsqueda
por mínimos: no falta ninguno de largo `≤ 24`. Lo único en la celda `d = 1` es el ciclo trivial (`ℓ ≤ 24`; ya sabido).

**3. Estructura (verificado en el rango; interpretación heurística).**
- `ω(d)` grande ⟺ `d` es (casi) un número de Collatz: el tipo dominante de 6487, 13085, 14197, 9823 es `(k, ℓ)` con
  `2^ℓ − 3^k = d` **exactamente** (p. ej. `6487 = 2^16 − 3^10`, 456 de sus 534 ciclos); en 14303, `B_{17,27} = 355·d`.
  Es lo esperable: si `d = B`, casi todos los collares de tipo `(k, ℓ)` tienen `gcd(A_P, B) = 1`.
- Mínimo vs `d`: mediana `x_min/d = 0,053`, p99 ≈ 61, máximo 517 (`d = 343`, `x = 177337`, `(k, ℓ) = (94, 149)`, exceso
  `ℓ − k log₂3 = 0,0135`): los mínimos grandes son ciclos **angostos** (`ℓ/k` pegado a `log₂3`), como dice la cota de
  Belaga. Los ciclos más largos (`k` hasta 2292, `ℓ/k ≈ 2,04`) tienen mínimos chicos (5–65).
- Sólo el 7 % de los primitivos son angostos (`ℓ = ⌈k log₂3⌉`); los `k` más frecuentes (12, 10, 24, 30, 17, 8, …) no son
  los denominadores de las convergentes de `log₂3` sino los `k` chicos con muchos `ℓ` admisibles: el tipo `(k, ℓ)` sólo
  es posible si `2^ℓ ≡ 3^k (mod d)`, un retículo de `ℤ²` que depende de `d`. **Para `d = 1` ese retículo es todo `ℤ²`**:
  `a = 1` es el denominador con *más* tipos candidatos, no con menos.
- De los 1481 `d` con un único ciclo primitivo, ese ciclo tiene `k = 1` sólo para `d = 1` (los `k = 1` primitivos son
  exactamente `d = 2^ℓ − 3`, `x = 1`), `k = 2` sólo para `d = 7`, y `k ≥ 3` en los otros 1479.

**4. El experimento que podía refutar el escepticismo: ¿la celda `d = 1` es estadísticamente rara?**
Si los denominadores `d_P` tuvieran una estructura no aleatoria que "empuja" lejos de `d = 1`, un enunciado uniforme podría
capturarla. Test (`fam_model.py` sobre la tabla de `fam_necklaces.py 24`): para cada `(k, ℓ)` y cada divisor `e | B`,
`c_e = #{P : e | A_P}` frente a cuatro modelos aleatorios: uniforme (`N/e`); con rango (`A_P < e` lo imposibilita);
**con mínimo** (`#{P : A_min(P) ≥ e}/e`: si `e | A_P`, el ciclo de `f_{B/e}` tiene todos sus elementos enteros `≥ 1`,
o sea `A_min ≥ e`); y mínimo con rango (`Σ ⌊A_min/e⌋/A_min`). En unidades de ciclos, `ℓ ≤ 24`, filas con `N ≥ 50`:

| banda `e/N` | esperado (unif., rango, mínimo, mín.+rango) | observado |
|---|---|---|
| `[10⁻³, 10⁻²)` | 4521, 4520, 4521, 4515 | 4486 |
| `[10⁻², 10⁻¹)` | 711, 708, 710, 701 | 684 |
| `[10⁻¹, 1)` | 87, 84, 84, 77 | 59 |
| `[1, 10)` | 9,1, 7,6, 5,1, 4,3 | 1 |
| `≥ 10` | 0,8, 0,35, 0,04, 0,03 | 0 |

Por denominador `D` (ciclos con `d_P | D`, `ℓ ≤ 24`, sin el trivial), modelo con mínimo vs observado:
`D = 1`: **1,52 vs 0** (P(Poisson ≤ 0) = 0,22; con mín.+rango 1,33); `D = 5`: 4,23 vs 3; `D = 7`: 2,32 vs 1;
`11`: 1,54 vs 2; `13`: 9,96 vs 9; `23`: 4,24 vs 2 (P = 0,21); `59`: 4,76 vs 6; total `1 < D ≤ 60`: 52,5 (50,5) vs 46.

Lectura (heurística): (i) en módulos chicos `A_P` está equidistribuido (error ≲ 1 %); (ii) en módulos `e ≳ N/10` hay un
**déficit sistemático moderado** (59 contra 77–87 en `[0,1; 1)`) que la positividad del mínimo explica sólo en parte;
no sé su causa (abierto); (iii) **`a = 1` no se destaca**: su cero (P = 0,22) es tan probable como el déficit de `D = 23`
(P = 0,21) o `D = 7` (P = 0,33), que sí tienen ciclos. Nada en los datos separa a `a = 1` de los `a` con ciclos no triviales.

## Formalización
No se formalizó nada: lo que hay en limpio (la partición por denominadores, `d_P | B`, la monotonía de abajo) es elemental
y no acerca la prueba. No encontré la ecuación de Böhm–Sontacchi en el repo (`Bridge.lean` y `Forge/` no la tienen
como teorema); si alguna vez hiciera falta, el lema "ciclo de `f_1` con vector `P` ⟹ ciclo de `f_a` con vector `P` para
todo `a`" es inmediato (multiplicar la órbita por `a`).

## Por qué falló / qué aprendimos
**Causa exacta: en la familia, `a = 1` es una celda de una partición, y la información uniforme en `a` sólo ve agregados
de celdas; la celda `d = 1` es justamente el módulo extremo `e = B`, el más difícil.**

1. **Todo enunciado uniforme es una combinación de los `c_e`.** Para un tipo `(k, ℓ)`, con `N` palabras y `B = 2^ℓ − 3^k`:
   `c_e = #{P : e | A_P} = k · Σ_{d | B/e} ω_{k,ℓ}(d)` para `e | B`. Cualquier suma sobre `a` de cantidades de ciclos
   (`Σ_{a ≤ X} w(a) ω_{k,ℓ}(a)`, identidades tipo `Σ_{d|B} ω_{k,ℓ}(d) = α_{k,ℓ}`, series `Σ_P d_P^{−s}`, `Σ_P gcd(A_P, B)`)
   es combinación lineal de los `c_e` con `e ≥ B/X`. La de `a = 1` es `k·ω_{k,ℓ}(1) = c_B`: aparece **sólo** con el módulo
   `e = B` (por inversión de Möbius no hay otra forma de aislarla). Promediar sobre `a ≤ X` permite usar módulos
   `e ≈ B/X` (donde equidistribución tipo Littlewood–Offord / Tao tiene chance), pero entonces `a = 1` pesa `1/X`.
   Es la brecha "distribucional → puntual" de las rondas 1–5 y 9 con otra cara: el factor que se gana promediando es
   exactamente el que se pierde al especializar (igual que en la ronda 9, donde hacía falta ver un solo árbol, `≍ 1/N₀`).
2. **Monotonía en la dirección equivocada.** Un ciclo de `f_1` con vector `P` da un ciclo (forzado) de `f_a` con el mismo
   vector para **todo** `a` (`d_P = 1` divide a todo). Así, "`f_a` no tiene ciclos de tipo `P`" para algún `a` implica lo de
   `a = 1`, pero es **más fuerte** y es falso para muchos `a`. Y "`P` es ciclo entero de 3x+1 ⟺ `P` es ciclo de `f_a` y de
   `f_{a'}` con `gcd(a, a') = 1`" es una reformulación tautológica (`d_P | a` y `d_P | a'`), no una palanca.
3. **Las cotas uniformes demostradas no llegan a cero.** Belaga (2003) y Belaga–Mignotte (1999) dan, uniformemente en `a`,
   perigeo `≤ a·k^C` y `#ciclos de largo impar k ≤ a·k^{32}`. Para `a = 1` eso es "a lo sumo polinomialmente muchos",
   no "ninguno". Es Baker, la misma herramienta que da los `m`-ciclos (ronda 4); no hay nada uniforme más fino.
4. **Filtro a = 5 (y 7, 13, …).** Un argumento por conteos no distingue `a = 1`: en el modelo aleatorio, `a = 1` espera
   ≈ 1,5 ciclos no triviales con `ℓ ≤ 24` (observa 0) y `a = 7` espera 2,3 (observa 1). En largos grandes ambos esperan
   ≈ 0, así que un enunciado "para todo `a`, los ciclos de `f_a` tienen `ℓ ≤ L(a)`" + cómputo **sí** pasaría el filtro,
   pero es la Conj. de Lagarias efectiva, estrictamente más fuerte que el caso `a = 1`, y abierta.
5. **Dualidad sin simetría.** El intercambio `A ↔ B` (Belaga–Mignotte, Conj. 3: ciclos que pasan por `n = 1`, o sea `A | B`)
   tiene infinitos candidatos y se cree verdadero infinitas veces; `B | A` (Collatz) tiene finitos por tipo. No hay
   involución que lleve uno al otro (la corona y los números de Collatz tienen formas distintas).

**Lo que queda (abierto, heurístico):** el déficit moderado de soluciones de `e | A_P` en módulos `e ≳ N/10`
(59 observados contra 77–87 esperados en `[0,1; 1)`, `ℓ ≤ 24`). Si fuera real y tuviera una causa estructural (no sólo la
positividad del mínimo), sería información sobre *todos* los denominadores chicos a la vez; pero, por (1), aun una
explicación completa daría "menos ciclos de denominador chico en promedio", no "ningún ciclo con `d = 1`".
