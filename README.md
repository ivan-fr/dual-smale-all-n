# All-Degree Structural and Asymptotic Lower Bounds for the Dual Smale Mean Value Conjecture

Pure **Lean 4.36.0** formalization (zero `sorry`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`, zero floating-point or external numerical dependencies) of four unconditional **all-degree ($n \ge 2$)** theorems on the Dual Smale Mean Value Conjecture:

$$\forall P(z) = z + a_2 z^2 + \dots + a_n z^n \in \mathbb{C}[z]\ (a_n \neq 0, n \ge 2), \qquad \max_{P'(\zeta) = 0} \left|\frac{P(\zeta)}{\zeta}\right| \ge \frac{1}{n}.$$

## Main Formally Verified Theorems (All $n \ge 2$)

1. **Theorem 1 — Supporting Half-Plane Exact $1/n$ Theorem + Strict Uniqueness** ([`DualSmale/HalfPlaneTheorem.lean`](lean/DualSmale/HalfPlaneTheorem.lean)):
   If $P$ has a critical point $\zeta_j \neq 0$ such that $\operatorname{Re}(\zeta_k/\zeta_j) \ge 1$ for all $k$ (equivalently $w_k = \zeta_j/\zeta_k \in \overline{D(1/2, 1/2)}$), then $|P(\zeta_j)/\zeta_j| \ge 1/n$ for all $n \ge 2$, with strict inequality for $n \ge 3$ unless $P(z) = \frac{1 - (1 - z/\zeta_j)^n}{n/\zeta_j}$.
   - Key algebraic discovery: $n(n - 1) G_n(w) = R_n(1 - w) := \sum_{j=0}^{n-2} (n - 1 - j)(1 - w)^j$, giving a 5-line Eneström–Kakeya proof of zero-freeness on $|1 - w| \le 1$.

2. **Theorem 2 — Sharp Zero-Free Disk, Elementary Polynomial Mountain Pass, and All-$n$ GWS Critical-Value Bound** ([`DualSmale/UnivalentCriticalValue.lean`](lean/DualSmale/UnivalentCriticalValue.lean)):
   - **Zero-Free Disk**: Every nonzero root $z_0$ of $P$ satisfies $|z_0| \ge 2\sin(\pi/n)\, r_{\min}(P)$ (sharp at $P_n$).
   - **Elementary Polynomial Mountain Pass**: Proved directly via an explicit continuous Newton-cutoff path deformation (zero covering spaces / Riemann–Hurwitz).
   - **Critical-Value Lower Bound**: $\max_{P'(\zeta)=0} |P(\zeta)| \ge \frac{49}{50\,n}\, r_{\min}(P) = \frac{0.98}{n}\, r_{\min}(P)$ for **every** $n \ge 2$!
   - **Equal-Modulus Dual Smale (98% for all $n \ge 2$)**: $|\zeta_1| = \dots = |\zeta_{n-1}| \implies \max_j |P(\zeta_j)/\zeta_j| \ge \frac{49}{50\,n}$.
   - **Bounded-Spread Dual Smale**: $\max_j |P(\zeta_j)/\zeta_j| \ge \frac{49}{50\,\kappa(P)\,n}$ ($\kappa = r_{\max}/r_{\min}$), strictly beating the $1/n^2$ literature barrier whenever $\kappa(P) < 0.98\,n$.

3. **Theorem 3 — Isolated Minimal Critical Point Theorem** ([`DualSmale/IsolatedAndLocal.lean`](lean/DualSmale/IsolatedAndLocal.lean)):
   If $|\zeta_k| \ge n|\zeta_j|$ for all $k \neq j$, then $|P(\zeta_j)/\zeta_j| > 5/18$ (an $n$-independent constant) and $|P(\zeta_j)/\zeta_j| \ge 1/n$ for all $n \ge 2$ (strictly for $n \ge 3$).

4. **Theorem 4 — Universal Strict Local Minimum Quadratic Form** ([`DualSmale/IsolatedAndLocal.lean`](lean/DualSmale/IsolatedAndLocal.lean)):
   For every $n \ge 3$, the second variation of $|n P(1)|^2$ on the closed unit polydisk around $P_n$ is strictly positive definite with explicit eigenvalue $\frac{n}{(n-1)^2(n-2)}$.

## Reproduction

```bash
cd lean
lake exe cache get
lake build DualSmale
lake env lean check_axioms.lean
```

Compile the paper PDF:
```bash
tectonic paper/dual_smale_all_n.tex
```

## Author & License
- **Author**: Ivan Besevic (ESIEE-IT, France — `ivan.besevic@edu.esiee-it.fr`)
- **License**: MIT (`LICENSE`)
