# 8. Clases forzadas

> Código: `Collatz/Forced.lean`, `Collatz/Forced/Certs.lean` (generado por `python3 scripts/drift_cert.py --lean`)

## La idea

No sabemos probar que toda órbita llega a 1. Pero sí podemos probar cosas del tipo: *si una órbita no llega a 1,
entonces tiene que pasar por ciertos lugares*. Por ejemplo: **toda órbita que no llega a 1 pasa por un número que
deja resto 2 al dividirlo por 8**. Se dice que la clase $\{2 \bmod 8\}$ está **forzada**.

¿Para qué sirve? Para achicar el problema. Si se probara que $\{7 \bmod 8\}$ está forzada, alcanzaría con
estudiar los números $\equiv 7 \pmod 8$: todo contraejemplo tendría que pasar por uno. Cuanto más chica la clase
forzada, más cerca estamos de saber dónde buscar (o de probar que no hay nada que buscar).

Yolcu, Aaronson y Heule probaron varias clases forzadas módulo 4 y 8 con reescritura, y dejaron abiertas cuatro:
$\{1\}$, $\{5\}$, $\{7\}$ y $\{5, 7\}$ módulo 8. Un paper de rStation (collatz_32, 2026) dio después un certificado
más simple. Este capítulo cuenta ese certificado, en una versión entera que formalizamos.

## La matemática

Fijemos un módulo $2^g$ y una clase candidata $A$. Supongamos una órbita $x_0, x_1, \dots$ (con el mapa clásico) que
no llega a 1 y **nunca** pasa por $A$. Queremos una contradicción.

### El grafo de residuos

Dibujamos el grafo cuyos nodos son los residuos $u \bmod 2^g$ fuera de $A$, con una flecha $u \to v$ si algún
número $\equiv u$ va en un paso a uno $\equiv v$. La órbita de residuos de $x_t$ es un camino infinito en ese grafo.

El certificado asigna a cada residuo un **nivel** que no sube a lo largo de las flechas. Como los niveles son
finitos, la órbita termina quedándose para siempre en un nivel. Hay dos tipos de nivel.

### Niveles de potencial: la energía que baja

En un nivel de potencial, el certificado da un entero $\Phi(u) \ge 0$ por residuo y un exponente $M$ tales que la
"energía"
$$E_t = x_t^{M} \cdot 2^{\Phi(x_t \bmod 2^g)}$$
se divide por 2 (al menos) en cada paso, mientras $x_t$ sea grande. Intuición: $M \log_2 x + \Phi$ es
$\log_2 x$ corregido por una "deuda" que depende del residuo. En un paso par, $\log_2 x$ baja 1. En un paso impar,
sube $\log_2 3 \approx 1{,}58$, y la deuda $\Phi$ tiene que pagar la diferencia. Que $E_t$ sea un natural que se
divide por 2 para siempre es imposible.

### Niveles de pin: el punto 2-ádico que no es entero

Si un nivel es un solo ciclo de residuos, todos los números que se quedan ahí siguen la misma sucesión de
paridades, periódica. Hay un único "número" 2-ádico que da vueltas por ese ciclo para siempre: el **pin**. Es un
racional $P/D$ (por ejemplo, $-1$ para la clase `…1111`, o los puntos del ciclo de $-5$).

Si $x_t$ se queda en ese ciclo, el entero $e_t = D x_t - P_t$ (con $P_t$ el pin escalado del residuo actual)
cumple:
- en un paso impar, $x \mapsto 3x + 1$ y $P \mapsto 3P + D$, así que $e \mapsto 3e$;
- en un paso par, $x \mapsto x/2$ y $P \mapsto P/2$, así que $e \mapsto e/2$.

En cada vuelta al ciclo, $e$ se divide por la misma potencia de 2. Un entero no nulo no se puede dividir por 2
infinitas veces, así que $e = 0$ y $x_t$ **es** el pin. Si el pin no es un entero positivo (salvo 1, 2, 4), es una
contradicción.

### Los números chicos

La energía sólo baja para $x$ grandes ($x \ge X_0$). Los chicos los cubre la verificación de CollatzForge: todo
número menor que 600 001 llega a 1.

**Teorema (corrección del certificado).** Si un certificado pasa el chequeo, toda órbita que no llega a 1 pasa
por $A$.

## En Lean

```lean
structure Cert where
  g : ℕ               -- módulo 2^g
  A : List (ℕ × ℕ)    -- la clase: pares (k, r) para "x ≡ r (mod 2^k)"
  a : ℕ
  M : ℕ
  X0 : ℕ
  D : ℕ
  lvl : BT ℕ          -- niveles
  pinF : BT Bool      -- ¿el nivel es de pin?
  phi : BT ℕ          -- potencial
  pin : BT ℤ          -- pines escalados

/-- **Corrección del certificado.** Si `c.check`, toda órbita que no llega a `1` pasa por `A`. -/
theorem forced (h : c.check = true) (n : ℕ) (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ t, ∃ p ∈ c.A, collatz^[t] n % 2 ^ p.1 = p.2
```

`check` es un programa que devuelve `true` o `false`, y `forced` es su teorema de corrección: el patrón de siempre.
Las tablas son árboles binarios (`BT`) indexados por los bits del residuo, para que el kernel las consulte en
$g$ pasos en lugar de recorrer una lista de $2^g$ elementos.

Cada clase concreta es una línea:

```lean
theorem forced_mod4_0 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 4 = 0 := by
  obtain ⟨t, p, hp, hx⟩ := (cert_mod4_0).forced (by decide +kernel) n hn h
  ...
```

El kernel corre `check` sobre el certificado (`by decide +kernel`) y el resto es desempaquetar.

### Lo que está verificado

**[Lean]** 25 clases forzadas, con certificados generados por `scripts/drift_cert.py`:

- las diez de YAH módulo 4 y 8 (otra prueba, independiente de la de ellos);
- $\{6\}$ y $\{12\}$ módulo 16;
- las clases que collatz_32 presenta como nuevas: $\{9, 15\}$ y $\{11, 15\}$ módulo 16, $\{27, 28\}$ módulo 32 y
  nueve ternas módulo 32, como $\{7, 25, 30\}$;
- la más fuerte, `forced_Bc13`:

```lean
theorem forced_Bc13 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 = 7 ∨ collatz^[t] n % 8192 ∈ ([8187, 8178, 8185, 8172, 8182] : List ℕ)
```

Los cinco números raros son $-5, -14, -7, -20, -10$ módulo $2^{13}$: el ciclo negativo de $-5$. En palabras:
**toda órbita que no llega a 1 pasa por un número $\equiv 7 \pmod 8$ o por una sombra del ciclo de $-5$**.

Es lo más cerca que llega el método a la clase abierta $\{7\}$: lo que hay que agregar a "$7 \bmod 8$" son,
justamente, las sombras de un ciclo negativo. Con módulo $2^{14}$ esa clase ya no tiene certificado. El grafo
tiene 7163 nodos, y el kernel lo verifica en unos dos minutos.

## Qué es nuestro y qué no

- **[Literatura]** La idea del certificado (grafo de residuos + deriva + pines) y las clases nuevas son de
  collatz_32 (rStation, 2026, no arbitrado). Las clases módulo 4 y 8 son de YAH.
- **[Lean]** La versión entera del certificado ($x^M 2^\Phi$ en lugar de logaritmos y $Dx - P$ en lugar de
  2-ádicos), su prueba de corrección y la verificación de las 25 clases son nuestras.
- **[Literatura]** Las cuatro clases abiertas siguen abiertas. collatz_32 prueba que estos certificados no pueden
  con ellas en ninguna resolución, por la "barrera de signo": las sombras de los ciclos negativos
  ($-1$, $-5$, $-17$) se acumulan a toda profundidad. Nuestro certificador lo confirma: falla en las cuatro.

## Ejercicios

1. (Papel) Probá a mano que $\{0 \bmod 2\}$ está forzada. (¿Puede una órbita que no llega a 1 ser siempre impar?)
2. (Papel) Verificá que $-5, -14, -7, -20, -10$ módulo 8192 son 8187, 8178, 8185, 8172, 8182.
3. (Papel) El ciclo negativo $-1 \to -2 \to -1$ sigue las paridades impar, par, impar, par, … Mostrá que el único
   racional que sigue esa sucesión de paridades para siempre es $-1$. (Pista: resolvé $x = (3x+1)/2$.)
4. (Papel) En el argumento del pin, ¿por qué cada vuelta al ciclo divide a $e$ por una potencia de 2 *positiva*?
5. (Computadora) Corré `python3 scripts/drift_cert.py 3 8 5,7` (la clase $\{5, 7\} \bmod 8$, con grafo módulo
   $2^8$) y mirá dónde falla. Después probá `python3 scripts/drift_cert.py 4 6 9,15`, que sí funciona.
