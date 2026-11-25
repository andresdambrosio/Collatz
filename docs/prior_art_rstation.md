# Prior art: rStation (r/collatz) y densidad positiva — notas de lectura (2026-11-25)

rStation (rstation.ai) es un foro de agentes de IA con revisión por agentes. Al 25/11/2026 tiene **229 papers**
sobre Collatz, todos "accepted" por el foro. Ninguno está arbitrado por humanos, y varios dicen explícitamente
que nadie más revisó las pruebas. Se citan como preprints; cada uno lleva su propia etiqueta de estado
(PROVED / CHECKED / NUMERICAL). API: `https://rstation.ai/api/v1/problems/collatz/papers` (listado paginado) y
`https://rstation.ai/api/v1/papers/collatz_N/versions/1/download` (texto en markdown).

## Leídos completos

- **collatz_3** (two-path obstructions). Ninguna función potencial de la forma
  `H(n) + Φ(n mod M, v₂(n+1)) + βω(n) + γΩ(n) + R(Ω−ω)` (con `H` creciente y `Φ`, `R` arbitrarias) baja en
  todo paso impar acelerado por encima de cualquier umbral. Testigos: dos caminos positivos construidos a partir
  del ciclo negativo `(−5, −7)`, con extremos primos o libres de cuadrados (criba).
  → Es primo de nuestra "barrera de localidad" (LP de potenciales locales, testigos ralos). La arquitectura
  es distinta (ellos: residuos + factores primos; nosotros: conteo de patrones cortos + primeras/últimas cifras),
  pero la conclusión es la misma.
- **collatz_32** (drift certificates). Certificados `log₂x + Φ(x mod 2^g)` sobre el grafo de residuos más
  exclusión de ciclos ("pins"):
  - Teorema B: el certificado existe ⟺ toda medida ergódica de deriva ≥ 0 sobre el conjunto 2-ádico que evita
    `A` tiene entropía 0.
  - Corolario C: **refinar la resolución nunca prueba más**.
  - **Barrera de signo**: todos los fracasos vienen de puntos periódicos 2-ádicos con pin racional
    **negativo** (ciclos `−1`, `−5`, `−17` y una cascada `H_j` cerca de `−5`, a toda profundidad 2-ádica).
    Las clases abiertas de YAH son falsas en `ℤ∖{0}`, así que una prueba tiene que usar la positividad a escala
    2-ádica arbitrariamente fina.

  Certifica algunas clases nuevas mod 16 y mod 32, como `{9,15}`, `{11,15}` y `{27,28}`.
- **collatz_40** (normal witnesses + arctic). Cada clase abierta de YAH (`{1}`, `{5}`, `{7}`, `{5,7}` mod 8)
  contiene un punto 2-ádico de **cifras normales y deriva positiva** (decaimiento de Fourier a la Tao).
  - Teorema 3: ninguna interpretación ártica que lea desde la cifra menos significativa y cumpla la condición
    de fin (C-end) prueba esas clases, en una etapa o con eliminación de reglas.
  - Lema 6.1: excluir un ciclo racional `C` con certificados de grafo de residuos requiere resolución exacta
    `D(C) + 2`.
  - Lema 6.2: los autómatas árticos de "ciclos simples" no alcanzan.

  → Explica conceptualmente nuestros UNSAT árticos (C_2, C_3, d ≤ 4), aunque su teorema es sobre los
  sistemas de YAH y no sobre la escalera C_k.
- **collatz_66** (autómatas en toda base). Ningún conjunto `r`-automático invariante hacia adelante y sin
  puntos periódicos (en bases `2^a 3^b`) certifica una órbita divergente; en otras bases, esos conjuntos son
  ralos.
  - **Teorema B**: lo mismo vale para `5x ± 1`, cuyas órbitas se espera que diverjan. Así que la obstrucción
    por autómatas no distingue 3x+1 de 5x+1 y no es evidencia a favor de Collatz.
  - "Cerrar la brecha necesita información sobre las **cifras iniciales de órbitas individuales**".
  - Proposiciones C y D sobre cifras iniciales; collatz_203 dice que toda palabra aparece en las cifras iniciales
    de toda órbita no eventualmente periódica.

  → Es casi literalmente la síntesis de nuestras rondas 6–7: lo que no viaja es la interacción entre el tamaño
  y las últimas cifras.

## Leídos parcialmente (planteo y teoremas)

- **collatz_98**: funciones de ranking aditivas por ventanas, más términos de valuación, no certifican las clases
  abiertas. Generaliza el Teorema 7.1 de Nashida (usa el teorema de Host).
- **collatz_208**: los puntajes de cifras binarias (conteo de patrones, largo, unos, valuaciones) no fuerzan una
  bajada en `o(log n)` pasos, ni siquiera con reloj adaptativo.
- **collatz_86**: autómatas de cifras con signo (matrices reales fuertemente irreducibles y proximales, Λ > 0)
  no son funciones de ranking.
- **collatz_60**, **collatz_45**, **collatz_53**, **collatz_59**: interpretaciones naturales y reales
  no negativas, y lectores max-plus sin condición de fin. Extienden la barrera de Nashida a las clases abiertas y
  a `H`.
- **collatz_198**, **collatz_80**, **collatz_82**: mapas de Collatz polinomiales sobre `𝔽₂[x]` *distintos* del de
  Hicks et al.
  - El mapa de Matthews–Leigh, `((1+x)²f+1)/x`, es el análogo de 5x+1 y tiene una órbita divergente explícita.
  - Hay tablas con deriva negativa que igual divergen (por Frobenius).

  → No contradice nuestro borrador, porque el mapa `C_0` es el de Hicks, que sí está probado. Pero conviene
  aclarar que "el mundo polinomial" depende del mapa elegido.
- **collatz_10** (fourier_wren): `π_a(x) ≥ c·x/a` uniforme, **condicional** a la estimación de mezcla conjunta (J).
  - (J) está en collatz_5 y en `[LW-J]`.
  - Cita a Mazur [Ma26b], "Lean-formalised", para la densidad inferior positiva `c(a)·x` no uniforme: es M2 de
    ProofAtlas.
- **collatz_6**: versión en densidad *natural* del teorema de Tao (casi toda órbita alcanza valores casi
  acotados), vía joint mixing más teorema de renovación.

## Densidad positiva (ProofAtlas M2, auditado en `docs/audit_conjectureA.md`)

- M2: los predecesores de todo `a > 0` con `3 ∤ a` tienen densidad inferior positiva. Está en Lean y lo auditamos
  con nanoda.
  - Con `a = 1`: una fracción positiva de los enteros llega a 1.
  - Si `c` no converge, alguna iterada de `c` no es múltiplo de 3 (de las primeras dos, una no lo es), y sus
    predecesores tampoco convergen; por M2, los contraejemplos tendrían densidad inferior positiva.
  - Entonces **Collatz ⟺ los convergentes tienen densidad (inferior) 1**. Es un enunciado "distribucional"
    equivalente a la conjetura.

  No contradice a Tao: el conjunto de contraejemplos puede tener densidad positiva y aun así sus órbitas bajar
  hasta su mínimo. La lectura humana de la matemática de M2 sigue pendiente.

## Qué cambia para nosotros

1. **"Barrera de localidad" y certificados árticos (borrador `a-world-where-collatz-is-solved`)**: hay que citar
   collatz_3, 32, 40, 98 y 208 como trabajo paralelo con conclusiones equivalentes o más fuertes. La frase "Larger
   searches are running" está desactualizada: C_2 y C_3 con d = 4, B = 3 dieron UNSAT, y collatz_40 explica por qué.
2. **Síntesis "tamaño vs. últimas cifras"**: collatz_66 la enuncia de forma independiente ("leading digits of single
   orbits"), y collatz_32 da la versión 2-ádica (barrera de signo). Hay que presentarla como convergencia con ese
   trabajo, no como idea nueva.
3. **"Casi todos" (borrador del laboratorio y página de estado)**:
   - agregar M2: una fracción positiva llega a 1, verificado en Lean;
   - agregar que Collatz ⟺ densidad 1 de convergentes;
   - agregar collatz_6 (Tao en densidad natural, preprint de agentes).
   - El muro sigue siendo puntual: pasar de "densidad positiva" a "densidad 1" no es más fácil.
4. **Página de estado**: Hercher (≤ 91 mínimos locales) tiene una extensión de agentes a ≤ 166 (collatz_206),
   que habría que citar como preprint sin verificar. collatz_74 da más de 80 corridas para todo ciclo.
5. **Para el laboratorio**: las vías "certificado de tamaño fijo" (potenciales locales, autómatas, matrices
   naturales/árticas/reales, ventanas con valuaciones) están cerradas por varios lados y con teoremas. Lo que queda
   abierto en esa literatura:
   - interpretaciones que leen desde la cifra más significativa sin condición de fin (Remark 5.4 de collatz_40;
     collatz_53 avanza);
   - natural reducible con Λ = 0;
   - argumentos que usen la positividad a escala fina (barrera de signo);
   - información de cifras iniciales de órbitas individuales.

## Kurtz–Simon (2007): el original

- **Borrador de Academia.edu (26/12/2006), copia local, no se sube al repo.** Está incompleto: falta la Figura 1, la
  sección 3 está vacía y la bibliografía está rota. Lo que sí tiene:
  - Definición 1.2: funciones afines `a_i x + b_i`.
  - Teorema 1.5: el problema es Π₂-completo.
  - **Teorema 2.3**: toda máquina de registros `M` se convierte efectivamente en `M'` tal que
    `M` es total ⟺ `M'` se detiene desde toda configuración.

  El método del Teorema 2.3 es una doble simulación. La simulación externa avanza sólo cuando una simulación
  interna, acotada por un reloj (inner-clock, que siempre termina), confirma que el estado es consistente.
- **Lagarias, *Annotated Bibliography II*, ítem 48** (versión publicada, LNCS 4484):
  - define funciones con `a_i, b_i` racionales **no negativos**, igual que nuestro `agcf`;
  - su Teorema 1 dice: `M_e` es total ⟺ toda órbita de `g_e` llega a 1;
  - su Teorema 2 dice: GCP es Π₂⁰-completo;
  - Lagarias anota que **"es un paper de conferencia y no da pruebas detalladas"**.
  - La misma entrada enuncia a Conway como "¿alguna iterada `g^(i)(2^n)`, `i ≥ 1`, es potencia de 2?", que es
    exactamente nuestro `conway_undecidable`.
- **Comparación con nuestro Lean:**
  - La idea central (mortalidad más un cálculo interno acotado) es la de ellos; nuestro bucle externo con
    `F` recursiva primitiva y bucles `for` es una variante.
  - La parte aritmética (basura, pares de estados, `(n+1)/2`) es nuestra.
  - Su Teorema 1 tal cual ya está: `allReachOne_iff_total`. Elegimos `F(c, ⟨k,t⟩) = 0` cuando las entradas
    `0..k` terminan en `t` pasos, con `t` mínimo.
