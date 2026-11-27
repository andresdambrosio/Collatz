# 13. Problemas abiertos

> Código: `Collatz/Main.lean`. Plan: `PLAN.md`.

## Los dos `sorry`

Todo el libro converge acá:

```lean
theorem no_nontrivial_cycles : NoNontrivialCycles := by
  sorry

theorem no_divergent_orbits : NoDivergentOrbits := by
  sorry
```

**[Abierto]** Los dos. Lo que sabemos de cada uno está en los capítulos 4, 5 y 9.

## Preguntas más chicas, al alcance

1. **Las cuatro clases abiertas de YAH** ($\{1\}$, $\{5\}$, $\{7\}$, $\{5,7\}$ módulo 8). Los certificados del
   capítulo 8 no pueden con ellas. ¿Hay otro tipo de certificado que sí?
2. **¿$C_3$ diverge?** En la escalera de acarreos (capítulo 12), el crecimiento máximo encontrado parece de orden
   $\sqrt{L}$ para números de $L$ cifras. Probar que $C_3$ no diverge, o encontrar una órbita divergente, sería un
   primer escalón genuino.
3. **La conjetura C1 y la barrera de Presburger.** La conjetura C1 de la ronda 11 está verificada hasta radio 30 y
   dice que los puntos mixtos no bajan con ninguna regla finita no dirigida. Si se probara, saldría un teorema
   limpio: *ninguna prueba por descenso con reglas expresables en la aritmética de Presburger (sólo suma) alcanza*.
   Sería un teorema de barrera, no un avance hacia la prueba, pero diría con precisión qué ingrediente le falta a
   cualquier demostración.
4. **Formalizar barreras ajenas.** Las barreras de rStation (collatz_32, collatz_40) sólo están en papel.

## Lo que una prueba tendría que hacer

Si algo enseñó este recorrido, es la lista de requisitos:

- usar que el número es **3** (filtro de $5n+1$);
- usar que el número es **positivo** (filtro de los negativos y de sus sombras);
- decir algo sobre **cada** órbita, no sobre la mayoría (filtro de "casi todos" y brecha exponencial de Tao);
- leer **todo** el número, no ventanas ni últimas cifras (barreras de localidad y de signo);
- y no ser un método general, porque no lo hay (Conway, Kurtz–Simon).

Ninguna herramienta conocida cumple todo eso. Si algún día aparece una, este libro debería servir para chequearla
rápido.
