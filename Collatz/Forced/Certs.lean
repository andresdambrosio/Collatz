import Collatz.Forced

/-!
# Certificados concretos de clases forzadas (generado por `scripts/drift_cert.py --lean`; no editar)

Cada teorema dice: toda órbita de Collatz que no llega a `1` pasa por la clase indicada.
* `YAH`: clases probadas por Yolcu, Aaronson y Heule (2023), re-verificadas aquí con otro método.
* `{6}`, `{12}` mod 16: rStation collatz_32 (derivables de YAH).
* resto: la "base" de clases que collatz_32 reporta como no derivables de YAH por su test de clausura
  (fourier_wren, rStation, 2026; no arbitrado). Acá quedan verificadas en el kernel.
-/

namespace Collatz

namespace Forced

open Cert

def cert_mod4_0 : Cert where
  m := 2
  g := 2
  A := [0]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [0, 0, 1, 1]
  pinLvl := [false, true]
  phi := [0, 0, 0, 0]
  pin := [0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [0] mod 4 (YAH). -/
theorem forced_mod4_0 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 4 ∈ ([0] : List ℕ) :=
  (cert_mod4_0).forced (by decide +kernel) n hn h

def cert_mod4_1 : Cert where
  m := 2
  g := 2
  A := [1]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [1, 0, 0, 0]
  pinLvl := [true, true]
  phi := [0, 0, 0, 0]
  pin := [0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [1] mod 4 (YAH). -/
theorem forced_mod4_1 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 4 ∈ ([1] : List ℕ) :=
  (cert_mod4_1).forced (by decide +kernel) n hn h

def cert_mod4_2 : Cert where
  m := 2
  g := 2
  A := [2]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [0, 1, 0, 2]
  pinLvl := [true, false, false]
  phi := [0, 0, 0, 0]
  pin := [0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [2] mod 4 (YAH). -/
theorem forced_mod4_2 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 4 ∈ ([2] : List ℕ) :=
  (cert_mod4_2).forced (by decide +kernel) n hn h

def cert_mod4_3 : Cert where
  m := 2
  g := 2
  A := [3]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [0, 0, 0, 0]
  pinLvl := [false]
  phi := [0, 28, 16, 0]
  pin := [0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [3] mod 4 (YAH). -/
theorem forced_mod4_3 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 4 ∈ ([3] : List ℕ) :=
  (cert_mod4_3).forced (by decide +kernel) n hn h

def cert_mod8_2 : Cert where
  m := 3
  g := 3
  A := [2]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [3, 4, 0, 0, 2, 5, 1, 1]
  pinLvl := [false, true, false, true, false, false]
  phi := [0, 0, 0, 0, 0, 0, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [2] mod 8 (YAH). -/
theorem forced_mod8_2 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([2] : List ℕ) :=
  (cert_mod8_2).forced (by decide +kernel) n hn h

def cert_mod8_3 : Cert where
  m := 3
  g := 3
  A := [3]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [1, 1, 1, 0, 1, 1, 0, 0]
  pinLvl := [true, false]
  phi := [0, 28, 16, 0, 0, 28, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [3] mod 8 (YAH). -/
theorem forced_mod8_3 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([3] : List ℕ) :=
  (cert_mod8_3).forced (by decide +kernel) n hn h

def cert_mod8_4 : Cert where
  m := 3
  g := 3
  A := [4]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [0, 1, 3, 4, 0, 2, 5, 5]
  pinLvl := [true, false, false, false, false, true]
  phi := [0, 0, 0, 0, 0, 0, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [4] mod 8 (YAH). -/
theorem forced_mod8_4 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([4] : List ℕ) :=
  (cert_mod8_4).forced (by decide +kernel) n hn h

def cert_mod8_6 : Cert where
  m := 3
  g := 3
  A := [6]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [0, 0, 0, 1, 0, 0, 0, 2]
  pinLvl := [false, false, false]
  phi := [0, 28, 16, 28, 0, 28, 0, 28]
  pin := [0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [6] mod 8 (YAH). -/
theorem forced_mod8_6 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([6] : List ℕ) :=
  (cert_mod8_6).forced (by decide +kernel) n hn h

def cert_mod8_1_5 : Cert where
  m := 3
  g := 3
  A := [1, 5]
  a := 2
  M := 1
  X0 := 1
  D := 1
  lvl := [4, 0, 0, 1, 3, 0, 2, 2]
  pinLvl := [false, false, true, false, true]
  phi := [0, 0, 0, 0, 0, 0, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [1, 5] mod 8 (YAH). -/
theorem forced_mod8_1_5 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([1, 5] : List ℕ) :=
  (cert_mod8_1_5).forced (by decide +kernel) n hn h

def cert_mod8_1_7 : Cert where
  m := 3
  g := 3
  A := [1, 7]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0]
  pinLvl := [false]
  phi := [0, 0, 12, 40, 16, 28, 32, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [1, 7] mod 8 (YAH). -/
theorem forced_mod8_1_7 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 8 ∈ ([1, 7] : List ℕ) :=
  (cert_mod8_1_7).forced (by decide +kernel) n hn h

def cert_mod16_6 : Cert where
  m := 4
  g := 4
  A := [6]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [4, 4, 4, 5, 4, 4, 0, 0, 4, 3, 4, 6, 2, 4, 1, 1]
  pinLvl := [false, true, false, false, false, false, false]
  phi := [0, 28, 16, 28, 0, 28, 0, 28, 0, 28, 16, 28, 28, 28, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [6] mod 16 (c32). -/
theorem forced_mod16_6 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 16 ∈ ([6] : List ℕ) :=
  (cert_mod16_6).forced (by decide +kernel) n hn h

def cert_mod16_12 : Cert where
  m := 4
  g := 4
  A := [12]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [1, 1, 1, 2, 1, 1, 4, 5, 1, 0, 1, 3, 0, 1, 6, 6]
  pinLvl := [false, false, false, false, false, false, true]
  phi := [0, 28, 16, 28, 0, 28, 28, 28, 0, 28, 16, 28, 0, 28, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [12] mod 16 (c32). -/
theorem forced_mod16_12 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 16 ∈ ([12] : List ℕ) :=
  (cert_mod16_12).forced (by decide +kernel) n hn h

def cert_mod16_9_15 : Cert where
  m := 4
  g := 4
  A := [9, 15]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  pinLvl := [false]
  phi := [0, 66, 26, 92, 0, 66, 52, 118, 0, 0, 26, 92, 40, 66, 80, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [9, 15] mod 16 (c32b). -/
theorem forced_mod16_9_15 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 16 ∈ ([9, 15] : List ℕ) :=
  (cert_mod16_9_15).forced (by decide +kernel) n hn h

def cert_mod16_11_15 : Cert where
  m := 4
  g := 4
  A := [11, 15]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  pinLvl := [false]
  phi := [0, 118, 80, 92, 40, 66, 52, 118, 0, 118, 26, 0, 40, 66, 80, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [11, 15] mod 16 (c32b). -/
theorem forced_mod16_11_15 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 16 ∈ ([11, 15] : List ℕ) :=
  (cert_mod16_11_15).forced (by decide +kernel) n hn h

def cert_mod32_27_28 : Cert where
  m := 5
  g := 5
  A := [27, 28]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 0, 0, 1, 6, 6]
  pinLvl := [false, false, false, false, false, false, true]
  phi := [0, 66, 26, 92, 0, 66, 54, 92, 0, 92, 26, 92, 14, 66, 92, 92, 0, 66, 40, 92, 0, 66, 54, 92, 0, 80, 26, 0, 0, 66, 0, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1]

/-- Toda órbita que no llega a `1` pasa por [27, 28] mod 32 (c32b). -/
theorem forced_mod32_27_28 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([27, 28] : List ℕ) :=
  (cert_mod32_27_28).forced (by decide +kernel) n hn h

def cert_mod32_1_27_30 : Cert where
  m := 5
  g := 5
  A := [1, 27, 30]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
  pinLvl := [false, false, false]
  phi := [0, 0, 26, 92, 40, 66, 52, 118, 0, 118, 26, 92, 40, 66, 80, 118, 0, 66, 80, 92, 0, 66, 52, 118, 0, 118, 26, 0, 40, 66, 0, 118]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [1, 27, 30] mod 32 (c32b). -/
theorem forced_mod32_1_27_30 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([1, 27, 30] : List ℕ) :=
  (cert_mod32_1_27_30).forced (by decide +kernel) n hn h

def cert_mod32_7_25_30 : Cert where
  m := 5
  g := 5
  A := [7, 25, 30]
  a := 317
  M := 200
  X0 := 12825
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
  pinLvl := [false, false, false]
  phi := [0, 476, 277, 437, 158, 318, 238, 0, 0, 476, 119, 595, 199, 318, 357, 595, 0, 476, 277, 437, 158, 318, 398, 556, 0, 0, 119, 595, 158, 318, 0, 595]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [7, 25, 30] mod 32 (c32b). -/
theorem forced_mod32_7_25_30 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([7, 25, 30] : List ℕ) :=
  (cert_mod32_7_25_30).forced (by decide +kernel) n hn h

def cert_mod32_7_27_30 : Cert where
  m := 5
  g := 5
  A := [7, 27, 30]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
  pinLvl := [false, false, false]
  phi := [0, 92, 52, 92, 26, 66, 52, 0, 0, 106, 26, 118, 40, 66, 80, 118, 0, 92, 66, 92, 26, 66, 80, 118, 0, 106, 26, 0, 40, 66, 0, 118]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [7, 27, 30] mod 32 (c32b). -/
theorem forced_mod32_7_27_30 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([7, 27, 30] : List ℕ) :=
  (cert_mod32_7_27_30).forced (by decide +kernel) n hn h

def cert_mod32_9_27_30 : Cert where
  m := 5
  g := 5
  A := [9, 27, 30]
  a := 65
  M := 41
  X0 := 1193
  D := 1
  lvl := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
  pinLvl := [false, false, false]
  phi := [0, 66, 26, 92, 0, 66, 52, 118, 0, 0, 26, 92, 14, 66, 80, 118, 0, 66, 40, 92, 0, 66, 52, 118, 0, 80, 26, 0, 40, 66, 0, 118]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [9, 27, 30] mod 32 (c32b). -/
theorem forced_mod32_9_27_30 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([9, 27, 30] : List ℕ) :=
  (cert_mod32_9_27_30).forced (by decide +kernel) n hn h

def cert_mod32_18_19_31 : Cert where
  m := 5
  g := 5
  A := [18, 19, 31]
  a := 317
  M := 200
  X0 := 12825
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 3, 1, 0, 1, 1, 1, 0]
  pinLvl := [false, false, false, false]
  phi := [0, 318, 119, 437, 0, 318, 238, 556, 80, 675, 119, 437, 279, 398, 357, 675, 0, 318, 0, 0, 0, 318, 238, 556, 80, 675, 199, 675, 279, 398, 478, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [18, 19, 31] mod 32 (c32b). -/
theorem forced_mod32_18_19_31 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([18, 19, 31] : List ℕ) :=
  (cert_mod32_18_19_31).forced (by decide +kernel) n hn h

def cert_mod32_18_23_31 : Cert where
  m := 5
  g := 5
  A := [18, 23, 31]
  a := 317
  M := 200
  X0 := 12825
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 3, 1, 0, 1, 1, 1, 0]
  pinLvl := [false, false, false, false]
  phi := [80, 318, 119, 675, 0, 398, 478, 556, 80, 675, 199, 437, 279, 398, 357, 675, 80, 318, 0, 675, 0, 398, 238, 0, 80, 675, 199, 675, 279, 398, 478, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [18, 23, 31] mod 32 (c32b). -/
theorem forced_mod32_18_23_31 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([18, 23, 31] : List ℕ) :=
  (cert_mod32_18_23_31).forced (by decide +kernel) n hn h

def cert_mod32_18_29_31 : Cert where
  m := 5
  g := 5
  A := [18, 29, 31]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 3, 1, 0, 1, 0, 1, 0]
  pinLvl := [false, false, false, false]
  phi := [0, 28, 12, 40, 0, 28, 24, 52, 0, 64, 12, 40, 32, 28, 36, 64, 0, 28, 0, 40, 0, 28, 24, 52, 16, 64, 12, 64, 32, 0, 48, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [18, 29, 31] mod 32 (c32b). -/
theorem forced_mod32_18_29_31 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([18, 29, 31] : List ℕ) :=
  (cert_mod32_18_29_31).forced (by decide +kernel) n hn h

def cert_mod32_19_22_31 : Cert where
  m := 5
  g := 5
  A := [19, 22, 31]
  a := 27
  M := 17
  X0 := 147
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 3, 1, 1, 1, 0]
  pinLvl := [false, false, false, false]
  phi := [0, 64, 48, 40, 32, 28, 24, 64, 16, 64, 12, 64, 32, 64, 36, 64, 0, 64, 48, 0, 32, 28, 0, 52, 16, 64, 48, 64, 32, 64, 48, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [19, 22, 31] mod 32 (c32b). -/
theorem forced_mod32_19_22_31 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([19, 22, 31] : List ℕ) :=
  (cert_mod32_19_22_31).forced (by decide +kernel) n hn h

def cert_mod32_22_29_31 : Cert where
  m := 5
  g := 5
  A := [22, 29, 31]
  a := 317
  M := 200
  X0 := 12825
  D := 1
  lvl := [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 3, 1, 0, 1, 0]
  pinLvl := [false, false, false, false]
  phi := [0, 597, 398, 437, 199, 318, 238, 675, 0, 597, 119, 675, 279, 318, 357, 675, 0, 597, 398, 437, 199, 318, 0, 556, 199, 597, 119, 675, 279, 0, 478, 0]
  pin := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Toda órbita que no llega a `1` pasa por [22, 29, 31] mod 32 (c32b). -/
theorem forced_mod32_22_29_31 (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, collatz^[t] n % 32 ∈ ([22, 29, 31] : List ℕ) :=
  (cert_mod32_22_29_31).forced (by decide +kernel) n hn h

end Forced

end Collatz
