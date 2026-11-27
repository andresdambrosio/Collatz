# 6. Collatz como un juego de palabras

> Código: `Collatz/Rewriting.lean`, `Collatz/Rewriting/AllWords.lean`

## La idea

En 2021, Emre Yolcu, Scott Aaronson y Marijn Heule ([YAH, 2023](99-bibliografia.md)) tradujeron la conjetura a un
problema de **reescritura de palabras**: un juego en el que se reemplazan pedazos de una palabra según una lista
fija de reglas. La pregunta "¿todo número llega a 1?" se convierte en "¿este juego termina siempre, juegues como
juegues?".

¿Para qué cambiar de idioma? Porque para la terminación de juegos de reescritura hay una teoría enorme y
herramientas automáticas que buscan **certificados** de terminación (capítulo 7). Si alguna de esas herramientas
encontrara un certificado para el juego completo, eso sería una demostración de Collatz verificable por
computadora.

## La matemática

### Números como palabras

El alfabeto tiene siete letras:

- dos cifras **binarias**: `f` (cero) y `t` (uno);
- tres cifras **ternarias**: `0`, `1`, `2`;
- dos marcadores de borde: `▷` (principio) y `◁` (final).

Una palabra `▷ w ◁` se lee de izquierda a derecha arrancando con el valor 1 en `▷`:

| letra | efecto sobre el valor $x$ |
|---|---|
| `f` | $x \mapsto 2x$ |
| `t` | $x \mapsto 2x + 1$ |
| `d` ∈ {`0`,`1`,`2`} | $x \mapsto 3x + d$ |

Así, `▷t◁` vale $2 \cdot 1 + 1 = 3$, y `▷ft◁` vale 5 ($1 \to 2 \to 5$). Leer sólo binario es escribir el número en
binario con un 1 adelante implícito. Un mismo número tiene muchas escrituras mezclando bases: `▷2◁` también vale 5.

### Las 11 reglas

| Regla | Qué le hace al valor |
|---|---|
| `f◁ → ◁` | divide por 2 un par: $2y \mapsto y$ |
| `t◁ → 2◁` | manda un impar $2y+1$ a $3y+2 = \frac{3(2y+1)+1}{2}$ |
| `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | nada |
| `▷0 → ▷t`, `▷1 → ▷ff`, `▷2 → ▷ft` | nada |

Las dos primeras son el mapa acelerado: dividir por 2 es borrar la última cifra binaria, y $(3n+1)/2$ es cambiar
la última cifra binaria `t` por una cifra ternaria `2`. Las seis del medio pasan una cifra binaria por encima de una
ternaria sin cambiar el valor. Por ejemplo, `f1` hace $x \mapsto 2x \mapsto 6x + 1$, y `0t` hace
$x \mapsto 3x \mapsto 6x + 1$. Las tres últimas reescriben en binario una cifra ternaria que llegó al principio:
`▷1` vale $3 \cdot 1 + 1 = 4$, igual que `▷ff`.

La idea es que la multiplicación por 3 se hace "perezosamente": se anota una cifra ternaria al final y las reglas
del medio la van empujando hacia la izquierda hasta que se disuelve en binario. El 3 completo:

```text
▷t◁ → ▷2◁ → ▷ft◁ → ▷f2◁ → ▷1f◁ → ▷fff◁ → ▷ff◁ → ▷f◁ → ▷◁
 3     5     5      8      8      8       4      2     1
```

**Teorema (YAH, Teorema 3.17).** Collatz es cierta **si y sólo si** el juego termina siempre, empezando desde
cualquier palabra `▷w◁` y eligiendo las reglas como sea.

*Demostración.* La clave es una clasificación de los pasos.

**Lema (clasificación).** Todo paso o bien aplica $T_{\rm ac}$ al valor (las dos reglas dinámicas), o bien
conserva el valor y baja estrictamente la medida
$$\mu(w) = (\text{cantidad de cifras ternarias},\ \text{cantidad de pares (binaria, ternaria) con la binaria a la izquierda}),$$
ordenada lexicográficamente.

En efecto, las reglas del medio no cambian la cantidad de ternarias pero deshacen una "inversión", y las de inicio
borran una ternaria.

($\Rightarrow$) Si el valor de `▷w◁` llega a 1 en $k$ pasos de $T_{\rm ac}$, por inducción en $k$ y, dentro, en
$\mu$: cada paso del juego o baja $k$ en uno o deja $k$ fijo y baja $\mu$. Como el orden lexicográfico en
$\mathbb{N} \times \mathbb{N}$ no tiene cadenas descendentes infinitas, no hay jugadas infinitas.

($\Leftarrow$) Toda palabra no vacía admite algún paso (se comprueba mirando su última letra y la primera). Si el
juego termina desde `▷w◁`, inducción sobre la terminación: si $w$ es vacía, vale 1. Si no, hay un paso
$w \to w'$, la órbita del valor de $w'$ llega a 1 por inducción, y el valor de $w'$ es el de $w$ o su imagen por
$T_{\rm ac}$. En los dos casos, la órbita del valor de $w$ llega a 1. Como todo $n \ge 1$ es el valor de alguna
palabra (su escritura binaria), sale Collatz. $\blacksquare$

## En Lean

```lean
inductive Sym | f | t | d0 | d1 | d2

def Sym.act : Sym → ℕ → ℕ
  | .f, x => 2 * x
  | .t, x => 2 * x + 1
  | .d0, x => 3 * x
  | .d1, x => 3 * x + 1
  | .d2, x => 3 * x + 2

def valFrom (x : ℕ) (w : List Sym) : ℕ := w.foldl (fun x s => s.act x) x

/-- Valor de `▷ w ◁`. -/
def val (w : List Sym) : ℕ := valFrom 1 w
```

Los marcadores `▷` y `◁` no se representan: una palabra es la lista de letras del medio, y las reglas que tocan un
borde se escriben como "al final de la lista" o "al principio de la lista".

```lean
inductive Step : List Sym → List Sym → Prop
  | endF (u : List Sym) : Step (u ++ [.f]) u
  | endT (u : List Sym) : Step (u ++ [.t]) (u ++ [.d2])
  | f0 (u v : List Sym) : Step (u ++ .f :: .d0 :: v) (u ++ .d0 :: .f :: v)
  ...
  | s0 (v : List Sym) : Step (.d0 :: v) (.t :: v)
  | s1 (v : List Sym) : Step (.d1 :: v) (.f :: .f :: v)
  | s2 (v : List Sym) : Step (.d2 :: v) (.f :: .t :: v)

/-- El sistema termina sobre toda palabra canónica `▷ w ◁`. -/
def Terminates : Prop := ∀ w, Acc (fun y x => Step x y) w
```

`Step` es un **predicado inductivo**: `Step w w'` quiere decir "de `w` se pasa a `w'` en un paso", y hay un
constructor por regla. `u ++ v` es concatenar y `s :: v` es poner `s` adelante. `endF u`, por ejemplo, dice que de
`u ++ [f]` (la palabra `u` seguida de `f◁`) se pasa a `u`.

`Acc` es la forma de Lean de decir "no hay cadenas infinitas a partir de acá" (*accesible*). Formalmente, `w` es
accesible si todo `w'` al que se llega en un paso es accesible. Es inductivo, así que **no hay forma de construir
una prueba de `Acc` para un `w` desde el que se pueda jugar para siempre**. `Terminates` pide eso para toda palabra.

El lema de clasificación:

```lean
/-- Todo paso es dinámico (aplica `Collatz.T`) o conserva el valor y baja la medida. -/
theorem Step.classify {w w' : List Sym} (h : Step w w') :
    val w' = Collatz.T (val w) ∨ (val w' = val w ∧ LexLt (μ w') (μ w))
```

`Collatz.T` es el mapa **acelerado** de CollatzForge, y `μ w = (tc w, inv w)` es la medida de la prueba de papel.

El teorema:

```lean
/-- **Yolcu–Aaronson–Heule, Teorema 3.17 (forma canónica).** La conjetura de Collatz equivale
a la terminación del sistema de reescritura de 11 reglas sobre las palabras `▷ w ◁`. -/
theorem collatz_iff_terminates : Collatz ↔ SRS.Terminates
```

### Todas las palabras

El Teorema 3.17 del paper habla de la terminación sobre **todas** las palabras del alfabeto de siete letras,
incluidas las raras, como `◁◁t▷0`, con marcadores en cualquier lado. El Lema 3.16 del paper reduce eso a las
palabras canónicas. `Collatz/Rewriting/AllWords.lean` lo prueba:

```lean
theorem collatz_iff_terminatesAll : Collatz ↔ SRS.TerminatesAll
```

La idea: toda regla tiene lado izquierdo de dos letras y no crea ni borra marcadores. Por eso un paso en una
palabra de la forma `A m B`, con `m` un marcador, es en realidad un paso en `A m` o en `m B`, y la palabra termina
si terminan los dos pedazos. Cortando en cada marcador, queda un pedazo sin marcadores adentro, con a lo sumo un
marcador en cada punta. Si falta el `▷` de la izquierda, las reglas de inicio no se pueden usar y baja la medida
(cantidad de binarias, inversiones). Si falta el `◁` de la derecha, no se pueden usar las dinámicas y baja
(cantidad de ternarias, inversiones). El único caso que queda es `▷x◁`, que es el teorema anterior.

## Qué es nuestro y qué no

- **[Literatura]** La reformulación y el teorema son de Yolcu, Aaronson y Heule.
- **[Lean]** La formalización es nuestra. La prueba de ($\Leftarrow$) es distinta de la del paper: ellos simulan
  la órbita con una estrategia fija ("reescribir siempre lo más a la derecha posible"), y nosotros usamos
  "toda palabra no vacía tiene un paso" más la clasificación, que es más corto. Nuestra prueba del Lema 3.16
  también es distinta. Al intentar formalizar la estrategia del paper encontramos un hueco menor (capítulo 7).

## Ejercicios

1. (Papel) Verificá que las seis reglas del medio conservan el valor. (Una ya está hecha arriba.)
2. (Papel) Escribí la partida completa desde `▷ft◁` (el 5) hasta `▷◁`.
3. (Papel) ¿Por qué hace falta la regla `▷0 → ▷t`? Encontrá una palabra que, sin ella, no pueda seguir jugando
   aunque su valor no sea 1.
4. (Papel) Explicá por qué $\mu$ baja en la regla `t1 → 2f`. ¿Cuántas inversiones se deshacen?
5. (Lean) Probá `SRS.val [.f, .t] = 5` con `rfl` o `decide`.
