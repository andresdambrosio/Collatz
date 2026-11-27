# 7. Certificados de terminación

> Código: `Collatz/Rewriting/Natural.lean`, `Arctic.lean`, `Subsystems*.lean` (generados), `Farkas.lean`,
> `FarkasCert.lean` (generado), `Neighbors.lean`

## La idea

Un **certificado** es un objeto finito y concreto que se puede chequear mecánicamente y que, una vez chequeado,
garantiza un enunciado infinito. Es la idea central de este capítulo y una de las del libro.

El ejemplo de juguete: si a cada letra le asignás un **peso** (un natural) de modo que *cada regla baje
estrictamente el peso total* de la palabra, el juego termina, porque un natural no puede bajar para siempre. Los
pesos son el certificado: son pocos números, y chequear que cada regla baja es una cuenta finita. Pero la
conclusión vale para las infinitas palabras y las infinitas partidas.

Para el juego de Collatz, un certificado así sería una demostración de la conjetura. No se conoce ninguno, y en
este capítulo vemos por qué es tan difícil encontrarlo y qué se sabe hacer.

## La matemática

### Interpretaciones matriciales

Los pesos por letra son demasiado pobres. En la práctica se usan **matrices**. A cada letra $x$ se le asigna una
función afín $[x](v) = M_x v + c_x$ sobre vectores de $\mathbb{N}^d$. A una palabra se le asigna la composición, y
el "peso" de `▷w◁` es la primera coordenada de $[\,▷w◁\,](0)$. Si todas las matrices tienen entradas naturales,
la composición es **monótona**: si un pedazo de la palabra baja, la palabra entera baja. Por eso alcanza con
chequear las reglas, que son finitas, comparando matrices entrada por entrada.

Hay dos aritméticas típicas:

- **naturales**: la suma y el producto de siempre;
- **árticas** (o *max-plus*): la "suma" es el máximo y el "producto" es la suma, con $-\infty$ como "cero". Una
  matriz ártica $d \times d$ es un autómata con $d$ estados donde cada letra suma un puntaje según el estado, y el
  peso de una palabra es el puntaje del mejor camino.

### Sacar reglas de a una

Pedir que *todas* las reglas bajen el peso es mucho. La técnica clave es más modesta.

**Teorema (eliminación de reglas).** Sea $S$ un conjunto de reglas y $S_1 \subseteq S$. Supongamos una medida
$\varphi$ que no sube en ningún paso de $S$ y baja estrictamente en los pasos de $S_1$. Si el sistema $S
\setminus S_1$ termina, entonces $S$ termina.

*Demostración.* En una partida infinita de $S$, $\varphi$ nunca sube y baja cada vez que se usa una regla de
$S_1$. Entonces se usan reglas de $S_1$ sólo finitas veces, y a partir de cierto momento la partida es una partida
infinita de $S \setminus S_1$. Contradicción. $\blacksquare$

Así se puede ir sacando reglas de a una, con un certificado distinto para cada una, hasta que no queda nada.

### Lo que se puede y lo que no

- **[Literatura]** YAH encontraron con computadora certificados para cada uno de los **11 subsistemas** que se
  obtienen borrando *una* regla: cada uno termina. También probaron así la convergencia de una variante de Collatz
  de Farkas (2005), que no tiene ciclos falsos. Es un resultado lindo: un teorema de tipo Collatz probado
  enteramente por una computadora.
- **[Literatura]** El sistema completo es otra cosa. **Nashida (2026, formalizado en Lean)** demostró que las
  interpretaciones matriciales naturales y árticas, usadas solas, **nunca** pueden sacar ni una sola regla del
  sistema completo, en ninguna dimensión.

### El filtro de los vecinos

Una manera de entender por qué el sistema completo es duro, con la idea del filtro de $5n+1$ del capítulo 1.
Cambiá la regla dinámica `t◁ → 2◁` por `t◁ → 1◁`. El juego nuevo simula, en los impares,
$x \mapsto (3x - 1)/2$, que **tiene ciclos** ($5 \to 7 \to 10 \to 5$). Ese juego no termina, y en él no se puede
sacar ninguna regla: para cada regla hay una partida cíclica que la usa.

Consecuencia: cualquier certificado que saque una regla del sistema de Collatz tiene que "ver" la diferencia entre
la cifra `2` y la cifra `1` *en esa única regla*. Un certificado que tratara igual a las dos serviría también para
el vecino, donde la conclusión es falsa.

## En Lean

### La eliminación de reglas

```lean
/-- **Eliminación de reglas con una medida.** Si `φ` no crece en ningún paso de `S` y baja
estrictamente en los pasos de `S₁`, la terminación de `S ∖ S₁` implica la de `S`. -/
theorem TermIn.removal {S S₁ : RuleName → Bool} (φ : List Sym → ℕ)
    (hle : ∀ ρ w w', S ρ = true → IStep ρ w w' → φ w' ≤ φ w)
    (hlt : ∀ ρ w w', S ρ = true → S₁ ρ = true → IStep ρ w w' → φ w' < φ w)
    (hrest : TermIn (fun ρ => S ρ && !S₁ ρ)) : TermIn S
```

Un conjunto de reglas es una función `RuleName → Bool` ("¿esta regla está?"), y `TermIn S` es "el subsistema `S`
termina sobre las palabras canónicas".

### Las interpretaciones

```lean
/-- Función afín `x ↦ M x + v` sobre `ℕ^d`. -/
structure Aff (d : ℕ) where
  M : Fin d → Fin d → ℕ
  v : Fin d → ℕ

def app (f : Aff d) (x : Vec d) : Vec d := fun i => (∑ j, f.M i j * x j) + f.v i
def ge (f g : Aff d) : Prop := (∀ i j, g.M i j ≤ f.M i j) ∧ ∀ i, g.v i ≤ f.v i
def gt (f g : Aff (d + 1)) : Prop := f.ge g ∧ g.v 0 < f.v 0
```

`ge f g` es la comparación entrada por entrada que garantiza $f(x) \ge g(x)$ para todo $x$, y `gt` además pide que
la primera coordenada baje estrictamente. `TermIn.removal_nat` (y su versión ártica, `TermIn.removal_arc`)
convierte un certificado en una aplicación de `TermIn.removal`. Las hipótesis son comparaciones de matrices
concretas, que el kernel chequea con `decide +kernel`. Así queda un subsistema en el archivo generado:

```lean
theorem termIn_without_r06 : TermIn (fun ρ => ρ != .r06) :=
  TermIn.removal_arc I_T06_1 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T06_2 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  ...
```

Se lee: "sin la regla 6, saco la 10 con el certificado `I_T06_1`, después la 9 con `I_T06_2`, …". Y el resumen:

```lean
theorem termIn_without : ∀ ρ : RuleName, TermIn (fun σ => σ != ρ)
```

### Farkas y un hueco en el paper

```lean
def F (n : ℕ) : ℕ :=
  if n % 3 = 1 then (n - 1) / 3 else if n % 6 = 0 ∨ n % 6 = 2 then n / 2 else (3 * n + 1) / 2

theorem farkas_convergent : ∀ n, 1 ≤ n → ∃ k, SRS.Farkas.F^[k] n = 1
```

En la §4.2 del paper se dice que reescribir siempre "lo más a la derecha posible", desde la escritura ternaria,
simula la trayectoria completa. No es así: esa estrategia se traba en tres palabras cortas, `▷t◁` (3), `▷f◁` (2) y
`▷ft◁` (5), cuando se acaban las cifras ternarias. La conclusión se salva con un invariante (a lo sumo dos cifras
binarias al principio y el resto ternarias): la forma final vale a lo sumo 7, y esos valores se chequean a mano.
El teorema está bien. Es un hueco menor, de los que sólo aparecen cuando una computadora te obliga a escribir
cada paso.

### Los vecinos

```lean
/-- **En el vecino `3x − 1` no se puede eliminar ninguna regla:** `SN(ρ/𝒯₁)` es falso para
toda regla `ρ`. -/
theorem not_relSN_d1 (ρ : RName) : ¬ WellFounded (fun y x => RelStep .d1 ρ x y)
```

La prueba es un ciclo concreto de 315 pasos que usa todas las reglas, generado por `scripts/neighbors.py` y
chequeado por el kernel. `not_relSN_d0` hace lo mismo para el vecino $3x - 3$.

## Qué es nuestro y qué no

- **[Literatura]** Los certificados son de YAH (repositorio `emreyolcu/rewriting-collatz`). La barrera es de
  Nashida.
- **[Lean]** El verificador de interpretaciones naturales y árticas, y la re-verificación de todos los
  certificados de YAH, son nuestros. En lo que encontramos, nunca se habían verificado en un asistente de
  demostración. El hueco de la §4.2 y su arreglo son nuestros. El filtro de los vecinos también.
- **[Experimento]** Probamos además matrices con entradas racionales (fuera del alcance de Nashida) sin encontrar
  nada en las cotas buscadas.

## Ejercicios

1. (Papel) Mostrá que el sistema con sólo las seis reglas auxiliares termina. (Pista: contá inversiones.)
2. (Papel) Mostrá que el sistema sin las dos reglas dinámicas termina. ¿Qué medida usarías?
3. (Papel) Encontrá pesos naturales por letra que prueben que el sistema formado por `f◁ → ◁` y las seis
   auxiliares termina. ¿Por qué es fácil?
4. (Papel) Verificá que el vecino $x \mapsto (3x-1)/2$ tiene el ciclo $5 \to 7 \to 10 \to 5$.
5. (Para pensar) En el teorema de eliminación, ¿para qué hace falta que $\varphi$ no suba en las reglas de
   $S \setminus S_1$? Construí un ejemplo donde, sin esa condición, la conclusión falla.
