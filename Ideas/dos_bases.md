# Idea: certificados que leen el número en base 2 y en base 3 a la vez

**Estado:** cerrada para potenciales locales (ronda 10). Test exacto: las ventanas no mejoran nada, ni en una base ni en dos.
**Frente:** ambos (una potencial que baja en cada paso excluye divergencia y ciclos grandes)

## Enunciado
Todas las barreras conocidas (potenciales locales, autómatas, interpretaciones matriciales, ventanas, cifras
iniciales) leen el número en **una** base. Por Cobham, lo que es finito en las bases 2 y 3 a la vez es trivial, así que
un certificado que mire ambas escrituras queda fuera de esos marcos. Además, `3n+1` es local en base 3 (corrimiento) y
`/2` es local en base 2. Pregunta: ¿existe
`Φ(n) = log n + Σ w₂(ventanas del binario) + Σ w₃(ventanas del ternario)` con `Φ(S(n)) ≤ Φ(n) − δ` para todo `n` impar
grande (`S` = Syracuse)? Una potencial de un paso existe si y sólo si Collatz es cierta (el tiempo de parada sirve),
así que lo único que se prueba es la expresividad de las ventanas locales en dos bases.

## Filtro de barreras
- 5x+1: el ingrediente propio es la base 3 (el multiplicador). Control previsto: bases 2 y 5 para 5x+1.
- Positividad: leer escrituras finitas excluye los ciclos negativos de entrada (los negativos son 2-ádicos infinitos).

## Evidencia numérica (`scripts/two_base_potential.py`, planos de corte sobre muestras)
| ventanas (k₂, k₃) | cota de pesos B | δ* (máximo descenso alcanzable) |
|---|---|---|
| (6, 0) | 0,69 | −0,0111 (constante en L = 40…320) |
| (6, 4) | 0,42 | −0,0106 → −0,0161 al crecer L |
| (6, 0) y (6, 4) | 50 (sin piso) | **−0,00938 los dos, idéntico**: el ternario no aporta |
| (8, 0) / (8, 5) | 50 | −0,0040 / −0,0020 |
| (10, 0) | 50 | −0,0003 (sobreajuste: 2044 variables, 2400 filas) |

- Todos infactibles. Con ventanas grandes el método por muestras pierde poder (sobreajusta); el método exacto con
  autómatas (ronda 6) ya mostró que el binario solo es infactible para todo `n`.
- Las restricciones activas (duales) son sobre todo números **típicos** (densidad de unos ≈ 0,5, `v` = 1, 2, 3),
  más algunas tiras de unos.
- **Predicción refutada:** pensé que el cambio de las ventanas en un número al azar fluctúa como `√L` (ruido que mata
  los pesos). No: con los pesos óptimos el desvío de ΔΦ es constante en `L` = 40…1500. El LP elige pesos cuyo cambio en
  el volumen se cancela (telescópico).

## Estructura (por qué la parte de borde no aporta nada nuevo)
1. **Cifras bajas.** Por el teorema chino del resto, `n mod 2^a` y `n mod 3^b` son independientes. Y para `j ≥ b`,
   `n_j mod 3^b` depende **sólo de las últimas `b` valuaciones** (`n_j = (3^j n + c_j)/2^{V_j}`, y `3^j ≡ 0`). Verificado en
   20 000 órbitas para `b = 3, 5, 8`. O sea: las últimas cifras ternarias son memoria del pasado reciente de paridades;
   las binarias, el futuro cercano. Juntas: el residuo `n mod 6^k`.
2. **Cifras altas.** Las primeras cifras en base 2 y en base 3 son `{log₂ n}` y `{log₃ n}`: información de tamaño,
   acotada, y conjuntamente densa (log₂ 3 irracional).
3. **Sombras del ciclo de −1 (argumento elemental, riguroso).** Sea `n = 2^K m − 1`. Entonces `S^j(n) = 3^j 2^{K−j} m − 1`
   para `j ≤ K`, con `v = 1` en cada paso. Para `b ≤ j ≤ K − a` vale `S^j(n) ≡ −1 (mod 2^a 3^b)`: el residuo queda fijo
   mientras `log` crece `log(3/2)` por paso. Así que **toda** `Φ = log n + g(n mod 2^a 3^b) + (acotado)` crece a lo largo
   de la sombra si `K` es grande. La parte de borde de los certificados de dos bases está muerta.

Lo que queda: los términos de **volumen** (conteos de ventanas, no acotados). En binario, `×3` es un transductor finito
(desde la cifra menos significativa); en ternario, `/2^v` también lo es (división exacta desde la menos significativa, con
acarreo `< 2^v`). Los dos volúmenes sólo se acoplan a través de `v`.

## Test exacto (`scripts/two_base_exact.py`, sin muestras)
Mapa clásico, `V(n) = λ₂ L₂ + λ₃ L₃ + Σ f₂(ventanas binarias) + Σ f₃(ventanas ternarias)`, `f ≥ 0`,
`λ₂ + λ₃ log₃2 = 1` (así `V ≥ log₂ n − cte`).
- Paso par `n → n/2`: binario = corrimiento; ternario = transductor de división exacta por 2 (desde la cifra menos
  significativa, acarreo ∈ {0,1}). Se pide `ΔV ≤ −ε`.
- Paso impar: dos formulaciones. (i) `n → 3n+1` con `ΔV ≤ 0` (binario: transductor `n + 2n + 1`; ternario: agregar un
  `1`, cambio de borde). (ii) Modo `S`: `n → (3n+1)/2` (binario: transductor + corrimiento; ternario: transductor sobre
  `3n+1` + borde), con las dos bases como cotas independientes `Mb + Mt ≤ 0`. Si es factible con `ε > 0`, `V ≥ 0` baja sin
  cota (una órbita infinita tiene infinitos pasos pares puros: si no, `v = 1` siempre y `n = −1`), así que es un
  certificado para todo `n` grande; la independencia de las bases sólo agrega restricciones.
- "Para todo n" = camino más largo ≤ 0 en cada autómata (potenciales de nodos): LP exacto.
- Validación: los autómatas reproducen el cálculo directo de `ΔV` (0 discrepancias en 4 200 chequeos con pesos y números
  al azar). Un primer control dio "certificado" por un error (el peor borde ternario `M3` quedó libre en el control sólo
  binario); corregido.

**Resultados.** Infactible en todos los casos, en las dos formulaciones: (6,0), (8,0), (4,3), (6,3), (6,4), (7,4), (7,5),
(8,5). **Déficit** `K* = min (Mb + Mt)` con `ε = 0,01`: **exactamente 1** para (6,0), (8,0), (10,0), (6,4), (8,5) y (8,6),
alcanzado por la potencial trivial `V = L₂` con todas las ventanas en cero. Las ventanas no mejoran nada, ni en una base
ni en dos; el modelo no está sobrerrestringido (es factible y su óptimo es la solución trivial).

**Por qué.** `−1` es punto fijo de `n ↦ (3n+1)/2` en las dos bases a la vez (`…1111` en binario, `…2222` en ternario).
Los enteros `6^K m − 1` terminan en tiras largas de unos y de doses que sobreviven paso a paso mientras el número crece, y
los ciclos de los transductores (escrituras periódicas largas) obligan a que el cambio de ventanas en el volumen sea ≤ 0.
Es la "barrera de signo" (sombras de ciclos negativos, rStation collatz_32) apareciendo en las dos bases a la vez.

## Por qué falló / qué aprendimos
Leer en dos bases no rompe la barrera de signo: el ciclo de `−1` es un punto fijo 2-ádico **y** 3-ádico a la vez, así que
sus sombras se ven "quietas" en las dos escrituras. Las cifras ternarias bajas son memoria de las paridades recientes,
las altas son tamaño, y el volumen no puede compensar (ciclos de transductor). Lo que queda fuera de este test: potenciales
no locales (que no sean sumas de ventanas) y descenso por bloques de varios pasos.
