# 9. Collatz ⟺ casi todos llegan a 1

> Código: `Collatz/Density.lean`. Ver también `Ideas/tao_constante.md` y `scripts/tree_density.py`.

## La idea

En 2019, Terence Tao probó el resultado más fuerte que se conoce sobre Collatz: **casi todo número baja
muchísimo**. Pero "casi todo" no es "todo", y el filtro de "casi todos" del capítulo 1 dice que un argumento de
densidad nunca alcanza. ¿O sí?

Este capítulo cuenta una sorpresa: con un resultado de 2026 (la densidad positiva de los predecesores), la
conjetura *es equivalente* a un enunciado de "casi todos". La brecha entre "casi todos" y "todos" no desaparece,
pero se vuelve precisa y medible. Y medirla muestra que es enorme.

## La matemática

### Densidades

La **densidad natural** de un conjunto $S \subseteq \mathbb{N}$ es el límite (si existe) de
$$\frac{\#\{1 \le n \le x : n \in S\}}{x}.$$
Los pares tienen densidad $1/2$, los múltiplos de 3 densidad $1/3$, y los cuadrados densidad 0.

La **densidad logarítmica** pesa cada $n$ con $1/n$:
$$\frac{1}{\log x} \sum_{\substack{n \le x \\ n \in S}} \frac{1}{n}.$$
Si existe la densidad natural, la logarítmica existe y vale lo mismo. Al revés, no siempre.

### El teorema de Tao

**Teorema ([Tao, 2022](99-bibliografia.md)).** Sea $f$ cualquier función con $f(N) \to \infty$, por lenta que
sea (por ejemplo $\log \log \log \log N$). Entonces casi todo $N$, en densidad logarítmica, tiene en su órbita
algún valor menor que $f(N)$.

Es "Collatz para casi todos, salvo una constante que crece muy despacio". Si se pudiera tomar $f$ constante (por
ejemplo, $f = 2$), diría "casi todo número llega a 1". Tao advierte (Remark 1.4) que esa versión es
"probablemente casi tan difícil como la conjetura completa".

### Por qué "casi todos" alcanza, dado M2

**Hipótesis M2 (ProofAtlas, 2026; verificada en Lean por ellos, no arbitrada).** Para todo $a \ge 1$ no
divisible por 3, el conjunto de los $n$ cuya órbita pasa por $a$ tiene densidad inferior positiva: hay $c_a > 0$
con
$$\#\{n \le x : \text{la órbita de } n \text{ pasa por } a\} \ge c_a\, x$$
para todo $x$ grande. (Es una forma de la **Conjetura A** de Applegate y Lagarias, capítulo 11.)

¿Por qué "no divisible por 3"? Porque los múltiplos de 3 no tienen predecesores impares ($3m + 1$ nunca es
múltiplo de 3), y su árbol de predecesores es sólo $a, 2a, 4a, \dots$, de densidad 0.

**Teorema.** Suponiendo M2: Collatz $\iff$ el conjunto de los números que llegan a 1 tiene densidad 1. Lo mismo
con densidad logarítmica, y aun con densidad *superior* 1.

*Demostración.* ($\Rightarrow$) Si todos llegan, la densidad es 1.

($\Leftarrow$) Supongamos que $n_0$ no llega a 1. En su órbita hay un $a \ge 1$ no divisible por 3: si $n_0$ es
par, se baja hasta un impar, y si es impar, $3n_0 + 1$ no es múltiplo de 3. Ese $a$ tampoco llega a 1, y
**ningún** predecesor de $a$ llega a 1 (su órbita pasa por $a$). Por M2, los predecesores son al menos $c_a x$
de los $n \le x$. Entonces los que llegan a 1 son a lo sumo $(1 - c_a) x$, y la densidad no puede ser 1. Para la
versión logarítmica, la misma cuenta con pesos $1/n$, sumando por partes. $\blacksquare$

Moraleja: **si hay un contraejemplo, hay muchísimos**. Los contraejemplos no pueden estar aislados.

### ¿Cuánto falta?

Dicho así, Collatz es "el teorema de Tao con $f$ constante". La pregunta útil es **cuánto** falta, y se puede
medir.

- **[Literatura]** La prueba de Tao es cuantitativa. La proporción de $N$ cuya órbita nunca baja de $N_0$ es a lo
  sumo del orden de $(\log N_0)^{-c}$ para cierta $c > 0$. La pérdida está en su Proposición 1.17 (el decaimiento
  de Fourier de una variable aleatoria asociada a Syracuse).
- **[Experimento]** Del otro lado, un contraejemplo cuyo menor elemento es $m^*$ obliga a que esa proporción sea
  al menos la densidad del árbol de predecesores de un $a$ cercano a $m^*$. Medimos esas densidades
  (`scripts/tree_density.py`): para un $a$ típico son del orden de $1/a$. Por ejemplo, para $a = 10\,007$, unos 9
  de cada 10 000 números pasan por $a$.

Para llegar a una contradicción habría que bajar la cota de Tao de $(\log N_0)^{-c}$ a menos de $1/N_0$: una
brecha **exponencial**. Ni las mejoras que el propio Tao sugiere como posibles alcanzarían. $1/N_0$ es el tamaño de
la cuenca de *una sola órbita*, y pedirle a un método probabilístico que vea conjuntos tan finos es pedirle que vea
órbitas individuales.

## En Lean

```lean
def ReachesOne (n : ℕ) : Prop := ∃ k, iter k n = 1
def HitsVal (a n : ℕ) : Prop := ∃ k, iter k n = a

noncomputable def reachCount (x : ℕ) : ℕ := ((Finset.Icc 1 x).filter ReachesOne).card
noncomputable def predCount (a x : ℕ) : ℕ := ((Finset.Icc 1 x).filter (HitsVal a)).card

/-- Densidad natural inferior positiva de los predecesores de todo `a ≥ 1` no divisible por 3
(consecuencia de M2 de ProofAtlas; aquí, hipótesis). -/
def PredDensity : Prop :=
  ∀ a, 1 ≤ a → ¬ 3 ∣ a → ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop, c * x ≤ predCount a x
```

`noncomputable` aparece porque "llega a 1" no es decidible en general: Lean puede *contar* los elementos del
conjunto como objeto matemático, pero no tiene un programa que lo calcule. `∀ᶠ x in atTop` es "para todo $x$
suficientemente grande" (un *filtro* de Mathlib).

```lean
/-- **Collatz ⟺ casi todo entero llega a 1** (densidad natural 1, bajo `PredDensity`). -/
theorem collatz_iff_density_one (H : PredDensity) :
    Collatz ↔ Tendsto (fun x : ℕ => (reachCount x : ℝ) / x) atTop (𝓝 1)

theorem collatz_iff_logDensity_one (H : PredDensity) :
    Collatz ↔ Tendsto (fun x : ℕ => logSum ReachesOne x / Real.log x) atTop (𝓝 1)
```

`Tendsto f atTop (𝓝 1)` es "$f(x) \to 1$ cuando $x \to \infty$". Ojo: **M2 entra como hipótesis explícita**
(`H : PredDensity`). No la importamos: son unas 124 000 líneas en otra versión de Lean. Para no depender de una
transcripción a ciegas, copiamos el enunciado de M2 letra por letra y probamos que implica `PredDensity`
(`M2.predDensity_of_statement`). Dentro del proyecto de ProofAtlas comprobamos que su teorema prueba exactamente
ese enunciado (`scripts/m2_fidelity/`).

## Qué es nuestro y qué no

- **[Literatura]** La equivalencia **no es nuestra**: Lech Mazur la publicó en el blog de Tao (septiembre de
  2026), y la versión con densidad natural ya estaba en Lean en el paquete de ProofAtlas.
- **[Lean]** Lo propio es la versión logarítmica (la de Tao), la de densidad superior y el puente desde el
  enunciado literal de M2. La medición de la brecha exponencial es una lectura nuestra del paper de Tao.

## Ejercicios

1. (Papel) Mostrá que un múltiplo de 3 no tiene predecesores impares.
2. (Papel) Mostrá que el conjunto $\{2^k : k \ge 0\}$ tiene densidad natural 0. ¿Y densidad logarítmica?
3. (Papel) En la demostración de ($\Leftarrow$), ¿dónde se usa que el contraejemplo $a$ no es divisible por 3?
4. (Computadora) Estimá la densidad de los $n \le 10^7$ cuya órbita pasa por $a = 7$. ¿Y por $a = 10\,007$?
5. (Para pensar) ¿Por qué un teorema de "casi todos" con error $(\log N)^{-c}$ no puede ver un único contraejemplo?
