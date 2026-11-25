# Idea: deformar el análogo resuelto (𝔽₂[x]) hacia los enteros, metiendo acarreos

**Estado:** cerrada: la barrera aparece en k = 2 (ronda 6 del laboratorio, 2026-11-23)
**Frente:** ambos

## Enunciado
En 𝔽₂[x] el mapa `f ↦ f/x` (si `x | f`), `((1+x)f + 1)/x` (si no) lleva todo polinomio a 1
(Hicks–Mullen–Yucas–Zavislak 2008; Snapp–Tracy 2008). Leído en binario (`x = 2`) es **3n+1 sin acarreos**
(Monks 2025, arXiv:2508.10153: `n XOR 2n XOR 1`). Programa: una familia de problemas que vaya de 𝔽₂[x]
(resuelto) a ℤ (abierto) agregando acarreos de a poco; ver hasta dónde sobrevive la prueba y qué se rompe.

## Familia 1 — acarreo diferido: ℤ[2^{1/d}] — **descartada**
`R_d = ℤ[q]/(q^d − 2)`: `1 + 1 = q^d`, el acarreo salta `d` posiciones; `d = 1` son los enteros, y
`q^d → 0` q-ádicamente da 𝔽₂[q] en el límite. Mismo mapa con `q` en lugar de 2.
**Resultado (`scripts/carry_delay.py`):** para todo `d ≥ 2`, todas las órbitas divergen.
**Causa:** los positivos tienen tamaño real `Σ c_j 2^{j/d}`, y un paso impar seguido de sus divisiones multiplica,
en promedio, por `(1+q)/q²`. Eso es `> 1` apenas `q < φ`, o sea para todo `d ≥ 2`. Se pierde la contracción
`log 3 < 2 log 2`. Lección: una interpolación tiene que conservar el tamaño arquimediano del lado entero.

## Familia 2 — acarreos de vida limitada `C_k` — **viva**
`C_k(n) = n/2` si `n` es par; si `n` es impar, `(n + 2n + 1)/2` con un sumador binario donde cada acarreo tiene una edad:
nace con edad 1 cuando `aᵢ + bᵢ = 2` (o con el `+1` inicial), suma 1 al propagarse y se descarta si la edad pasa de `k`.
`k = 0` da 𝔽₂[x] (resuelto) y `k = ∞` da Collatz. Para `k` finito es un **código de bloques deslizante** (radio ~k)
seguido de un shift, cercano a los autómatas celulares. Script: `scripts/carry_trunc.py`.

### Evidencia numérica
| k | 3n+1: n < 20 000 | crecimiento máx. del largo (L = 10…160 bits) | 5n+1: escapes (n < 400) |
|---|---|---|---|
| 0 | todo → 1 | 0 (el largo nunca crece) | 115 |
| 1 | ciclos {1}, {0} | 0 | 0 |
| 2 | 8 ciclos, sin divergencia | 6, 10, 18, 37, 73 (~0,46 L) | 0 |
| 3 | ciclos {1,2}, {0} | 3, 4, 4, 4, 4 en la muestra; **no parece acotado**: ver "C_3 (24/11)" abajo | 0 |
| 4 | ciclos {1,2}, {0}, uno de largo 14 desde 47 | ~0,55 L | 260 |
| 6, 8, 12 | ciclos {1,2}, {0} | ~0,58 L (como ℤ) | 162–310 |
| ∞ | todo → 1 | ~0,58 L (`2^L − 1`) | 305 |

- `k ∈ {0, 1}`: el largo nunca crece, así que no hay divergencia por finitud (es trivial).
- `k = 2` y `k ≥ 4`: excursiones de tamaño lineal en L, como en ℤ, y aun así **ninguna divergencia** observada.
- **Filtro 5n+1:** para `k ≥ 4` el análogo de 5n+1 diverge (como en ℤ). Para `k = 1, 2, 3` no diverge:
  son degenerados.
- Hay ciclos espurios, así que "todo llega a 1" es falso para `C_k`. El análogo correcto es "**no hay órbitas divergentes**".

### Deriva media del largo (la "medida interpolada"), números de 4000 bits, 18 000 pasos por k
Deriva por paso = −½ + ½·P(acarreo llega arriba | impar). Con k = 0 vale −½ (grado exacto). Con k = ∞ vale
log₂3/2 − 1 ≈ −0,2075, y P = log₂(3/2) ≈ 0,585 (mantisa de Benford ≥ 2/3).

| k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 12 | ∞ |
|---|---|---|---|---|---|---|---|---|---|---|
| deriva | −0,50 | −1,00* | −0,26 | −0,62 | −0,23 | −0,34 | −0,22 | −0,21 | −0,22 | −0,21 |
| P(acarreo arriba) | 0 | 0 | 0,48 | 0,45 | 0,55 | 0,56 | 0,58 | 0,58 | 0,585 | 0,585 |

\* con k = 1 los acarreos perdidos vacían el número, que cae a 0: es degenerado.
- Los k pares son robustos a la definición de "edad": no cambian si el +1 inicial nace con edad 0, ni si en
  `s = 3` no se reinicia la edad. Los impares (3, 5) sí cambian: hay que tomar **k par** como familia canónica.
- **Lectura honesta:** desde k = 2 la estadística ya es la de Collatz (deriva negativa, mantisa que se mezcla).
  Probar "C_2 no diverge" vuelve a ser un enunciado puntual sobre una órbita. La barrera aparece **ya con
  acarreos de largo 2**. La única ventaja nueva es estructural: C_k es una regla local de radio acotado, y eso
  habilita invariantes regulares (tipo "closed tape languages" de bbchallenge) y reescritura con acarreos de vida finita.

## Experimento final: potencial local para C_2 (`scripts/carry_potential.py`) — no existe
Busqué `V(n) = L(n) + Σ f(ventanas de w bits)`, con `f ≥ 0`, que no suba en ningún paso impar con `L(n) ≥ L0`.
Si existiera, C_k no tendría órbitas divergentes. "Para todo n" es "camino más largo ≤ 0" en un autómata
ponderado, o sea un LP en (f, potenciales de nodos).
- Controles: `C_0` **factible** (f = 0, V = largo, la prueba de 𝔽₂[x]); Collatz exacto **infactible** (w = 3, 6).
- `C_2`: **infactible** para (w, L0) = (3,4), (4,6), (5,8), (6,10), (7,12).

**Por qué (explicación estructural, comprobada):** `n ↦ n + 2n + 1` con acarreos truncados es una biyección de ℤ₂
para todo k: cada bit de salida es el de entrada XOR una función de los bits de abajo (chequeado mod 2^m, m ≤ 14).
Entonces todos los C_k conservan la medida de Haar y son conjugados al shift 2-ádico, **igual que Collatz y que
𝔽₂[x]** (Monks). En el "volumen" del número, la dinámica es estadísticamente la de una sucesión aleatoria, y una
función local monótona paso a paso tendría que absorber fluctuaciones de los dos signos. Eso sólo se puede si no hay
crecimiento posible, que es el caso k = 0 (el largo nunca crece). En cuanto un acarreo puede llegar arriba (k = 2),
la prueba por grado se cae entera, no de a poco.

## Conclusión de la ronda
1. En el mundo 2-ádico, 𝔽₂[x], todos los C_k y Collatz son **el mismo sistema** (conjugados al shift).
   Lo único que los distingue es **qué elementos son "positivos" y cómo se mide su tamaño**: el grado o el log real.
2. La prueba de 𝔽₂[x] usa que el tamaño es exacto (no crece nunca). Basta un acarreo de largo 2 para que el
   tamaño fluctúe como en Collatz, y la dificultad aparece completa: **no viene de los acarreos largos**.
3. Cualquier prueba tiene que usar la interacción entre la estructura 2-ádica y el tamaño arquimediano. Los puentes
   puramente 2-ádicos (tilting, Witt, conjugaciones) no la ven.

## Reducción (fácil de formalizar)
Si en toda la órbita de `n` bajo Collatz ninguna cadena de acarreos de `n + 2n + 1` supera la edad `k`, entonces
esa órbita coincide con la de `C_k`. Por lo tanto:
**`C_k` sin divergencia ⇒ toda órbita divergente de Collatz tiene cadenas de acarreo arbitrariamente largas.**
Hay que ser honestos con lo que esto da: una órbita grande típica tiene cadenas de largo ~log₂(largo), que no
están acotadas. La reducción sólo excluye divergentes atípicas. El valor está en entender el **mecanismo**, no en la reducción.

## Filtro de barreras
- 5n+1: pasa para `k ≥ 4`.
- n > 0: sí (enteros con representación binaria finita).
- Más allá de mod 2^k y de "casi todos": la pregunta es puntual (cada órbita).
- Específico de 3n+1: depende de `n + 2n` contra `n + 4n`, por ahora sólo verificado numéricamente.

## Literatura
- Hicks–Mullen–Yucas–Zavislak, Amer. Math. Monthly 115 (2008) 615–622: todo polinomio llega a 1, con tiempo de parada ≤ deg² + 2·deg.
- Snapp–Tracy, JIS 11 (2008) 08.4.7.
- Monks, arXiv:2508.10153: 3n+1 sin acarreos en 𝔽₂[[q]]; conjugaciones en ℤ₂ (Teorema 2). No interpola.
- arXiv:2401.03210 y 2401.12781 (tiempos de parada en 𝔽₂[x]); Behajaina–Paran 2023 (𝔽_p[x]); arXiv:2510.07530 (variante binaria).
- Transductores y autómatas celulares para 3x+1 (Cloney–Goles–Vichniac 1987 y otros): emulan el mapa exacto, no truncado.
- **No encontré la familia `C_k` ni ninguna otra interpolación por acarreos** (búsqueda del 2026-11-23, no exhaustiva).

## Próximos pasos
1. Fijar la definición de "edad" (la anomalía de `k = 3` sugiere que depende del detalle) y elegir una canónica.
2. `C_2` es el caso no trivial más chico: excursiones lineales y sin divergencia observada. Preguntas: ¿hay una
   función potencial? ¿Es decidible "sin divergencia" para un código de bloques fijo? Ojo: muchos problemas de
   autómatas celulares son indecidibles en general, pero este es uno concreto.
3. Estudiar qué deja de valer de la prueba de 𝔽₂[x] (largo no creciente) en `k = 2`: dónde y cuánto crece el largo.
4. Lean: definir `C_k`, probar `C_0 =` mapa de 𝔽₂[x] (largo no creciente, sin divergencia) y la reducción de arriba.

## Reapertura (2026-11-23): potenciales con términos de borde y la barrera de localidad
`scripts/carry_potential2.py`: `V = L + Σ f(ventanas) + g(n mod 2^b) + h(b bits de arriba)`. Se minimiza la subida
inevitable t* en los pasos impares (t* = 0 sería una prueba de que no hay divergencia).

| | sólo ventanas (w = 3…8) | con bordes (w, b) = (4,2) | (6,4) | (8,6) |
|---|---|---|---|---|
| C_0 | 0 | 0 | | |
| C_2 | **1** | 0,5 | 0,5 | 0,5 |
| Collatz | **1** | 1 | 0,667 | 0,6 |

**Testigos (sacados del dual del LP):** números **ralos**, como `111010000010` o patrones con `100000000` repetido.
Son bloques aislados separados por ceros. Cada bloque evoluciona por su cuenta: el de abajo dicta la paridad
y el de arriba crece en los pasos impares. Ningún término local puede "saber" que la paridad de abajo va a compensar
después. Las órbitas de los testigos **no** crecen (sus largos oscilan y bajan). Lo que falla es la clase de certificado.
**Barrera de localidad:** un potencial que sea suma de términos locales más bordes acotados no certifica largo acotado,
ni en C_2 (t* se planta en 1/2) ni, aparentemente, en Collatz (1, 2/3, 3/5…, ¿tiende a 1/2?).
Hace falta un potencial **no local**, que lea todo el número (autómata con pesos, interpretación matricial).
Eso nos devuelve a la vía de reescritura, pero con un blanco más chico y local: C_2.

## Certificados de LARGO ACOTADO en reescritura (2026-11-23)
`scripts/carry_srs.py`: C_k como SRS. Una cabeza `H[p,c]` recorre la palabra de derecha a izquierda calculando
(n + 2n + 1)/2 con acarreos truncados. Reglas: `0◁ → ◁`, `1◁ → H◁`, `x H → H' o`, `▷H → ▷ o o`.
Simula exactamente a C_k (chequeado para n < 3000), y con k = ∞ (`K = -1`) a Collatz.
**Certificado:** interpretación monótona que oriente **débilmente** todas las reglas, con `[▷w◁] ≥ #bits`.
Implica que ninguna derivación tiene largo no acotado, o sea que no hay órbitas divergentes. Para Collatz eso sería
la mitad de la conjetura. **No lo cubre Nashida**, cuya barrera es sobre orientación estricta.

| sistema | naturales EWZ | árticas |
|---|---|---|
| C_0 | sat (d = 1) | sat (d = 1): todas las letras pesan 1 |
| C_2 | unsat: d = 1 (B ≤ 4), d = 2 (B ≤ 5), d = 3 (B ≤ 2) | unsat: d = 1, d = 2 (B ≤ 3); más grande, en curso |
| Collatz | unsat: d = 1 (B ≤ 4), d = 2 (B ≤ 2) | unsat: d = 2 (B ≤ 3) |

### Búsqueda SAT (CaDiCaL vía python-sat, `scripts/carry_srs_sat.py`) y núcleos insatisfacibles
- C_2 ártico: UNSAT en d = 3 con B ≤ 6 (7 min) y **UNSAT en d = 4 con B = 3** (2 h, 0,4 GB; corrida del 24/11).
  d = 5 (B = 3): **sin decidir** tras 3 h (corte por tiempo, 1 GB). Relanzado el 24/11 como cube and conquer
  (`scripts/run_cubes.sh`, 9 casos según M_0[0][0], M_1[0][0] ∈ {1,2,3}, ruptura de simetría): 5 casos UNSAT en
  segundos (los que tienen algún peso 3); (1,1), (1,2), (2,1), (2,2) **sin decidir en 8 h** con CaDiCaL 1.5.3 y 1.9.5. Con tope de 20 min, d = 4 (B = 5), d = 5 (B = 3, 5) y d = 6–8: sin respuesta.
- **Núcleos mínimos** (qué reglas bastan para la contradicción): en d = 1, 4 reglas, que son exactamente el paso
  3 → 5 de C_2 (`11 → 101`, gana un bit). En d = 2 y 3, la maquinaria de cabezas del ciclo falso 3 → 5 → 6 → 3.
- **C_2 tiene ciclos falsos de tamaño creciente** (máximo de bits 3, 6, 9, 11, 15, 18, 19, 20, 21… con arranques
  < 2·10⁵), probablemente infinitos. A diferencia de Collatz, en C_2 "todo llega a 1" es falso a todas las escalas.
- Congelamiento de los chicos (`rules(k, j)`: la cabeza cuenta los bits y no actúa arriba si hay < j): exacto para
  n ≥ 2^j. Collatz con j = 3, sin el ciclo trivial: sigue UNSAT en d ≤ 3. El núcleo en d = 1 es el paso
  7 → 11 (`111 → 1011`). La obstrucción no viene sólo de los ciclos: **cada paso de crecimiento de una órbita chica**
  tiene que pagarse con "crédito" que la cabeza trae, y en dimensión chica no alcanza.

## C_3 (2026-11-24): certificados, potencial verdadero y un crecimiento que no parece acotado
- **Certificados árticos para C_3:** UNSAT en d ≤ 3 (B = 3), también "bajo cero" (entradas ≥ −1, −2, −3;
  `neg` en `carry_srs_sat.py`, con chequeo independiente del modelo) y congelando los números < 2^j, j ≤ 5.
  **d = 4 (B = 3): UNSAT** (3 h 44 min). Controles: C_0 y C_1 dan SAT en todas las variantes. Los núcleos mínimos (d = 1) son pasos reales
  de crecimiento de la familia `11…1` (1 → 2, 7 → 11, 31 → 47), no palabras mal formadas del SRS.
- **Potencial verdadero** E(n) = (largo máximo futuro) − largo(n), n < 2^21. Clases de Myhill–Nerode (cota inferior de
  estados de un autómata determinista que calcule E exacto, ventanas de 8 cifras): C_0, C_1: 1 clase; C_3: 1, 2, 4, 8,
  15, 25, 44, 69, 104, 159, 244, 366, 532 (≈ ×1,5 por cifra, sin saturar); C_2: 2^p (todo prefijo distinto).
- **Corrección:** el "crecimiento acotado" de C_3 era un artefacto de mirar números chicos (máximo 6 con n < 2^21, 5 con
  muestras aleatorias de hasta 160 bits). Búsquedas dirigidas encuentran crecimiento cada vez mayor con prefijos más
  largos: prefijos de 4, 11, 15, 16 cifras seguidos de una tira de unos dan 6, 9, 10, 11 (exhaustivo); búsqueda en haz:
  13 (16 cifras), 15 (24), 17 (36), 19 (44 cifras + 80 unos; `1100111110011010111111110011111000110111…`).
  Con un prefijo fijo el crecimiento satura (prefijo de 40 cifras: 5, 7, 11, 17, 19, 19, 19 con 10…640 unos), y
  `2^R − 1` solo crece 1. Mecanismo: la tira de unos da muchos pasos impares seguidos, y en ese tiempo las cifras de
  arriba evolucionan por el triplicado truncado `g(x) = x + 2x` (acarreos de vida ≤ 3), que en promedio crece menos que
  ×2 (`largo(g^t(1)) − t`: 2, 4, −5, −7, −12, −18 para t = 10…60), pero para prefijos elegidos sostiene excedentes largos.
- Una sobreaproximación finita de las cifras de arriba (ventana de b + 5 cifras con el estado de abajo enumerado
  exacto) tiene ciclos de crecimiento positivo para b ≤ 8 (p. ej. `100 → 110 → 100`: dos pasos ×1,5): consistente con lo
  anterior. **Lo que queda abierto:** si C_3 diverge o no (crecimiento no acotado pero, en lo visto, sublineal: 19 cifras
  sobre 124) y a qué ritmo crece el máximo con el largo. Un certificado de largo acotado igual podría existir: sólo
  exige largo ≤ peso inicial ≤ B·largo + c.
- **Ritmo (cota inferior, búsqueda en haz sobre prefijo + tira de unos, `L` = largo total):** L = 16, 24, 32, 48, 64,
  96, 128, 192, 256 → crecimiento ≥ 5, 6, 7, 9, 11, 15, 19, 22, 25. `g/L` baja (0,31 → 0,10), `g/log₂L` sube
  (1,25 → 3,12) y `g/√L` se mantiene en 1,2–1,7: compatible con **crecimiento máximo ~ 1,5·√L** (sublineal, más rápido
  que logarítmico). Heurística: durante la racha de pasos impares, el excedente de las cifras de arriba sobre ×2 hace algo
  parecido a un paseo al azar sin deriva, cuya excursión típica en L pasos es ~√L. (En C_2 y en Collatz el excedente
  tiene deriva positiva y el crecimiento es lineal.) Es una cota inferior: la búsqueda puede no encontrar los peores casos.
