This Lean 4 code provides a formal proof of the **Eilenberg–Mazur swindle** (often called the Mazur swindle in knot theory). The theorem states that if an element $a$ in an additive commutative monoid equipped with a well-behaved, total infinite summation operator has an additive inverse ($a + b = 0$), then $a$ must be $0$.

---

## The Core Mathematical Argument

The structure `InfSum M` axiomatizes an infinite sum operator $S$ satisfying three properties:

1. **`sum_zero`**: $S(0, 0, 0, \dots) = 0$
2. **`cons`**: $S(x_0, x_1, x_2, \dots) = x_0 + S(x_1, x_2, \dots)$ (peeling off the first term)
3. **`pair`**: $S(x_0, x_1, x_2, x_3, \dots) = S(x_0 + x_1, x_2 + x_3, \dots)$ (grouping consecutive pairs)

Given $a + b = 0$, we define the alternating sequence:


$$X = (a, b, a, b, a, b, \dots)$$

We evaluate the total sum $S(X)$ in two different ways using our axioms:

* **Method 1 (Pairing directly):**

$$S(X) = S(a+b, a+b, a+b, \dots) = S(0, 0, 0, \dots) = 0$$


* **Method 2 (Peeling then Pairing):**
First, peel off the first term using `cons`:

$$S(X) = a + S(b, a, b, a, \dots)$$



Next, evaluate the remaining shifted sequence $Y = (b, a, b, a, \dots)$ by grouping its pairs:

$$S(Y) = S(b+a, b+a, b+a, \dots) = S(0, 0, 0, \dots) = 0$$



Substituting $S(Y) = 0$ back into the peeled equation yields:

$$S(X) = a + 0 = a$$



Equating both methods gives $a = 0$.

---

## Line-by-Line Tactic Breakdown

Here is exactly how the Lean proof automates this substitution using `simp_all +decide`:

```lean
have := S.pair ( fun i => if Even i then a else b );

```

* **Action:** Introduces the identity for pairing the sequence $X$.
* **Resulting local hypothesis:** $S(a, b, a, b, \dots) = S(a+b, a+b, \dots)$.

```lean
have := S.cons ( fun i => if Even i then a else b ) ; simp_all +decide [ Nat.even_add_one ] ;

```

* **Action:** Introduces the identity for peeling the first term of $X$, then simplifies the context.
* **Resulting local hypothesis:** Since $a + b = 0$, the first pairing hypothesis simplifies to $S(a, b, a, b, \dots) = S(0, 0, \dots) = 0$. Consequently, the peeling equation reduces to:

$$0 = a + S(b, a, b, a, \dots)$$


* *Note:* `Nat.even_add_one` changes parity definitions under index shifts (e.g., $(i+1)$ is even if and only if $i$ is odd).

```lean
have := S.pair ( fun i => if Odd i then a else b ) ; simp_all +decide ;

```

* **Action:** Instantiates the pairing rule for the shifted sequence $Y = (b, a, b, a, \dots)$.
* **Resulting local hypothesis:** Pairs up $(b+a, b+a, \dots)$. Because $b+a = a+b = 0$, `simp_all` immediately deduces:

$$S(b, a, b, a, \dots) = 0$$



```lean
simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
simp_all +decide [ add_comm, S.sum_zero ]

```

* **Action:** Substitutes the fact that $S(b, a, b, a, \dots) = 0$ into the equation $0 = a + S(b, a, b, a, \dots)$.
* **Result:** The expression becomes $0 = a + 0$, which simplifies directly to $0 = a$, closing the goal `a = 0`.
