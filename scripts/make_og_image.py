"""Genera site/assets/og.png (1200x630), la imagen de vista previa para redes (paleta cálida del blog)."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def orbit(n):
    out = [n]
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        out.append(n)
    return out

bg, fg, muted, accent = "#f6f0e4", "#2b2620", "#6e6458", "#9c4a1c"
fig = plt.figure(figsize=(12, 6.3), dpi=100, facecolor=bg)
ax = fig.add_axes([0.06, 0.12, 0.88, 0.42], facecolor=bg)
o = orbit(27)
ax.plot(range(len(o)), o, color=accent, lw=2.2)
ax.fill_between(range(len(o)), o, color=accent, alpha=0.08)
ax.set_yscale("log")
for s in ax.spines.values(): s.set_visible(False)
ax.tick_params(colors=muted, labelsize=11, length=0)
ax.set_xlim(0, len(o) - 1)
ax.text(len(o) - 1, 1.4, "27 → … → 1  (111 steps, peak 9,232)", ha="right", va="bottom", color=muted, fontsize=12, family="serif")
fig.text(0.06, 0.84, "Collatz in Lean", color=fg, fontsize=46, weight="bold", family="serif")
fig.text(0.06, 0.73, "An honest attempt to prove the Collatz conjecture,\nevery step checked by the Lean proof assistant.",
         color=fg, fontsize=20, family="serif", va="top", linespacing=1.35)
fig.text(0.06, 0.04, "Andrés D'Ambrosio · @andresdambrosio", color=muted, fontsize=15, family="serif")
fig.text(0.94, 0.04, "andresdambrosio.github.io/Collatz", color=accent, fontsize=15, family="serif", ha="right")
fig.savefig("site/assets/og.png", dpi=100, facecolor=bg)
print("ok")
