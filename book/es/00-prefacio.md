# 0. Prefacio

## Qué es este libro

Es el cuaderno de bitácora de un proyecto con un objetivo desmesurado: **intentar demostrar la conjetura de
Collatz**, en público, verificando cada paso con un asistente de demostración, Lean 4.

Desmesurado porque la conjetura lleva casi noventa años abierta, y matemáticos muy buenos dicen que la matemática
actual no tiene las herramientas para atacarla. Paul Erdős decía que "la matemática todavía no está lista para
problemas como este". No tenemos la ilusión de resolverla en una tarde. Lo que sí podemos hacer es:

1. **Verificar formalmente** lo que se sabe: reducciones, cotas, reformulaciones. Muchas de esas cosas sólo
   existían en papel, y en el camino encontramos huecos y pruebas circulares.
2. **Mapear las barreras**: entender, con teoremas y experimentos, por qué cada familia de métodos falla. Una
   barrera bien entendida le ahorra trabajo al próximo que lo intente.
3. **Registrar los fracasos** con su causa exacta. En un problema así, los fracasos son la mayor parte del
   trabajo, y casi nadie los publica.

## A quién está dirigido

A cualquiera que sepa qué es una división, una potencia y un poco de álgebra de secundario, y que tenga ganas
de pensar. Los capítulos van subiendo de nivel: los primeros se leen sin saber nada, y los de la Parte III y IV
usan algo de matemática universitaria (inducción, congruencias, logaritmos, algo de computabilidad). Cada
concepto se explica la primera vez que aparece.

No hace falta saber Lean. El capítulo 2 explica lo necesario y cada capítulo comenta el código línea por línea.
Si querés, podés saltear todas las secciones "En Lean" y leer el libro como un libro de matemática.

## Cómo leerlo

Cada capítulo tiene, en general, la misma estructura:

- **La idea**: qué queremos capturar y por qué importa.
- **La matemática**: definiciones y teoremas, con demostraciones en papel.
- **En Lean**: cómo está escrito en el repositorio y qué hace cada parte.
- **Qué es nuestro y qué no**: de quién es cada idea.
- **Ejercicios**: algunos de lápiz y papel, algunos de computadora y algunos de Lean.

## Cómo seguirlo con el código

```bash
git clone https://github.com/andresdambrosio/Collatz
cd Collatz
lake exe cache get   # baja Mathlib ya compilada
lake build
```

La primera compilación es larga (más de media hora) porque hay cálculos enormes que el kernel de Lean verifica uno
por uno: la cota de ciclos del capítulo 5, por ejemplo. Si `lake build` termina sin errores, todas las
demostraciones del libro marcadas **[Lean]** están verificadas en tu máquina. Para ver qué axiomas usa cada
teorema:

```bash
lake env lean scripts/Axioms.lean
```

## Cómo trabajamos: IA y verificación

Este proyecto se hace con ayuda intensiva de inteligencia artificial, y no lo escondemos: es parte del
experimento. La pregunta obvia es por qué confiar en algo escrito en buena parte por una IA. La respuesta tiene
tres partes.

**Las demostraciones no necesitan confianza.** Lean comprueba cada paso. Si el archivo compila, y `#print axioms`
muestra sólo los axiomas estándar, la demostración es correcta, la haya escrito quien la haya escrito.

**Los enunciados sí necesitan confianza.** Lean comprueba que demostramos *lo que escribimos*, no que lo escrito
sea *lo que queríamos decir*. Si definimos mal "ciclo", todos los teoremas sobre ciclos quedan perfectamente
verificados y son perfectamente irrelevantes. Por eso, en cada capítulo, mostramos la definición en Lean al lado
de la definición en papel y discutimos si dicen lo mismo. Esa comparación es la parte del libro que más vale la
pena leer con lápiz en la mano.

**La novedad necesita honestidad.** Una IA puede convencerse (y convencerte) de que encontró algo nuevo. Casi
nunca es así. La regla del proyecto es buscar antecedentes antes de creer en una idea, y decir explícitamente de
quién es cada cosa. Varias veces descubrimos, después de días de trabajo, que alguien ya lo había hecho. Lo
contamos.

## Las reglas del proyecto

1. Nunca declarar "demostrado" algo que use `sorry` (la marca de Lean para "falta probar esto"), axiomas nuevos,
   o hipótesis que equivalgan a la conjetura.
2. Antes de afirmar que un teorema está probado: que compile sin errores y que su lista de axiomas sea la
   estándar.
3. Lo que está abierto queda marcado con `sorry` y un comentario que explica qué falta.
4. **Calcular antes de formalizar.** Toda afirmación se prueba primero con Python en millones de casos. Recién si
   sobrevive, se escribe en Lean.
5. **Buscar el error antes de creer un éxito.** Si algo "funciona" demasiado bien, probablemente hay un bug.

## Otros textos del proyecto

- El [blog](https://andresdambrosio.github.io/Collatz/) cuenta los resultados de a uno, en inglés y en castellano.
- `docs/libro_collatz.md` es la bitácora cronológica completa: qué probamos, cuándo y en qué orden. Este libro, en
  cambio, está ordenado para aprender: no sigue el orden en que pasaron las cosas, sino el orden en que conviene
  entenderlas.
- `Ideas/LAB.md` es el laboratorio de ideas, con las once rondas de intentos.
