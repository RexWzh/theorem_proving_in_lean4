策略
=======

在这一章中，我们将介绍一种构建证明的替代方法，使用 *策略*。证明项是数学证明的一种表示；策略是一种命令或指令，描述如何构建这样的证明。简单地说，您可能开始一个数学证明时会说“为了证明正向推理，展开定义，应用前一个引理，并化简。”就像这些是告诉读者如何找到相关证明的指示一样，策略是告诉 Lean 如何构建一个证明项的指令。它们自然地支持一种逐步编写证明的风格，您可以将证明分解并逐步处理目标。

我们将由一系列策略组成的证明称为“策略样式”证明，以与我们目前已经见过的编写证明项的方式相对比，后者被称为“术语样式”证明。每种样式都有其优点和缺点。例如，策略样式的证明可能更难阅读，因为它们要求读者预测或猜测每个指令的结果。但它们也可以更短更容易编写。此外，策略为使用 Lean 的自动化提供了一个入口，因为自动化过程本身也是策略。

进入策略模式
--------------------

从概念上讲，陈述一个定理或引入一个``have``语句都会创建一个目标，即构造一个具有预期类型的项。例如，下面的代码会创建一个目标，需要构造一个类型为``p ∧ q ∧ p``的项，在上下文中有常数``p q : Prop``，``hp : p``和``hq : q``：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry
```

你可以将这个目标写成以下形式：

```
    p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
```

确实，在上面的例子中，如果你将 "sorry" 替换为空白符号，Lean 将报告这个目标没有被解决。

通常，你可以通过编写一个明确的术语来达成这个目标。然而，当需要一个术语的地方，Lean 允许我们插入一个 `by <tactics>` 块，其中 `<tactics>` 是一系列通过分号或换行符分隔的命令。你可以通过以下方式证明上述定理：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

我们通常将 ``by`` 关键字放在前一行，并将上面的示例写为：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

``apply``策略将一个表达式应用于一个被视为具有零个或多个参数的函数。它将当前目标的结论与表达式进行统一，并为剩余的参数创建新的子目标，前提是后续参数不依赖于它们。在上面的例子中，命令 ``apply And.intro`` 生成了两个子目标：

```
    case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p

    case right
    p q : Prop
    hp : p
    hq : q
    ⊢ q ∧ p
```

第一个目标通过命令 ``exact hp`` 实现。``exact`` 命令是 ``apply`` 的一种变体，用于指示给定的表达式应该完全填充目标。在策略证明中使用它是好的做法，因为它的失败会提示出现了问题。与 ``apply`` 相比，``exact`` 更可靠，因为在处理应用的表达式时，解析器会考虑目标的预期类型。然而，在这种情况下，``apply`` 也同样适用。

您可以使用 ``#print`` 命令查看生成的证明项（proof term）：

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test
```

你可以逐步编写一个策略脚本。在 VS Code 中，按下 ``Ctrl-Shift-Enter`` 可以打开一个窗口显示消息，当光标在策略块中时，该窗口会显示当前的目标。在 Emacs 中，按下 ``C-c C-g`` 会在任意行的末尾显示目标，或者在不完整的证明中将光标放在最后一个策略的第一个字符之后以查看剩余的目标。如果证明不完整，关键字 ``by`` 将会被一个红色波浪线标记，错误消息中也会包含剩余的目标。

策略命令可以接受复合表达式，而不仅仅是单个标识符。下面是前面证明的较短版本：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

不出意外，它产生了完全相同的证明术语。

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro hp
#  exact And.intro hq hp
#print test
```

多个策略应用可以通过分号连接在一行上写出。

这是因为 Lean 每行只执行一个策略应用，但是可以通过在每个策略应用之间添加分号来在一行中一次性应用多个策略。这种写法能够提高代码的紧凑性和可读性。

在 Lean 中，策略（tactic）是一种用于构造和变换证明的指令。它们可以被应用于目标（goal）或者证明的间断点（proof state）。策略的应用会改变目标或证明的状态，并且可以用于引入、消去、重写等操作。使用策略可以帮助我们更有效地构建证明。

例如，假设我们有两个策略 `tac1` 和 `tac2`，并且我们想在当前的目标上依次应用这两个策略。我们可以在一行中使用分号将它们连接起来，如下所示：

```lean
tac1; tac2
```

这将首先应用 `tac1` 策略，然后将 `tac2` 策略应用于产生的证明状态。通过这种方式，我们可以在一行中一次性应用多个策略，简化证明过程。

总而言之，通过在 Lean 中使用分号来连接多个策略的应用，我们可以在一行上写出多个策略的代码，提高代码的紧凑性和可读性。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

可能会产生多个子目标的策略通常会给它们加上标签。例如，策略 ``apply And.intro`` 将第一个子目标标记为 ``left``，第二个子目标标记为 ``right``。对于 ``apply`` 策略，标签是从 ``And.intro`` 声明中使用的参数名推断出来的。您可以使用记法 ``case <tag> => <tactics>`` 来结构化您的策略。以下是我们在本章中第一个策略证明的结构化版本。

```
Lemma and_commutative :
  forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  apply And.intro as left.
  case left.
    intros p q.
    apply And.intro.
      exact q.
      exact p.
Qed.
```

这个例子中，我们给 ``apply And.intro`` 的第一个子目标加上了标签 ``left``。然后，我们根据标签来结构化策略并进行证明。在 ``case left`` 中，我们使用了 ``intros p q`` 来引入标记为 ``left`` 的子目标的假设，并使用 ``apply And.intro`` 来继续证明。最后，我们使用了 ``exact`` 策略来完成证明。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

你可以使用``case``符号在解决``left``之前解决子目标``right``：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

请注意，Lean 将其他目标隐藏在 ``case`` 块中。我们称之为“聚焦”在所选目标上。此外，如果所选目标在 ``case`` 块结束时没有完全解决，Lean 会报错。

对于简单的子目标来说，可能没有必要使用标签选择子目标，但你可能仍然希望结构化证明。Lean 还提供了“bullet”符号的记法``. <策略>``（或 ``· <策略>``）用于结构化证明。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

基本策略
-------------

除了 `apply` 和 `exact` 外，另一个有用的策略是 `intro`，它引入了一个假设。接下来是一个在前一章中我们在命题逻辑中证明的恒等式的例子，现在我们将使用策略来证明它。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```

``intro`` 命令可以更一般地用于引入任意类型的变量：

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

可以使用它来介绍几个变量：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

正如``apply``策略用于交互式构建函数应用一样，``intro``策略用于交互式构建函数抽象（例如，``fun x => e``形式的项）。与lambda抽象记法一样，``intro``策略允许我们使用隐式的``match``。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

你还可以像 ``match`` 表达式一样提供多个选择。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

``intros`` 策略可以在没有参数的情况下使用，此时它会选择变量的名称并引入尽可能多的变量。您即将看到一个示例。

``assumption`` 策略会查找上下文中与当前目标匹配的假设，如果找到匹配的假设，则应用该假设。

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```

必要时，它会统一结论中的元变量：

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

下面的示例使用 ``intros`` 命令自动引入三个变量和两个假设：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```

请注意，默认情况下，Lean 自动生成的名称是不可访问的。这么做的目的是确保你的策略证明不依赖于自动生成的名称，从而使其更加健壮。但是，你可以使用组合子 ``unhygienic`` 来取消此限制。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

你还可以使用 ``rename_i`` 策略来重命名上下文中最近不可访问的名称。
在下面的例子中，策略 ``rename_i h1 _ h2`` 重命名了上下文中最后三个假设中的两个。

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```

``rfl`` 策略是 ``exact rfl`` 的语法糖。

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl
```

``repeat`` 组合子可以用来多次应用一种策略。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

有时候，另一种有用的策略是``revert``策略，从某种意义上说，它是``intro``的逆向操作。

```lean
example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

将一个假设移动到目标中，可以得到一个蕴含关系：

```
H : P
============================
P
```

In Lean, we can write this as:

```
example (P : Prop) (H : P) : P := H
```

Here, `P` represents a proposition (an assertion or a statement), and `H` represents a proof or evidence for `P`. The goal is to prove `P` using the hypothesis `H`. In Lean, the `example` keyword is used to introduce a new theorem or lemma. The proof is simply the hypothesis `H` itself, as it already provides the evidence needed to prove `P`. Therefore, by applying `H` as the proof, we can conclude that `P` is true.

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

但是 ``revert`` 更加聪明，不仅会还原上下文中的一个元素，还会还原依赖于它的所有后续元素。例如，在上面的例子中，还原 ``x`` 会同时带回 ``h``：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

您也可以一次撤销多个上下文元素:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

你只能 ``revert`` 本地上下文中的一个元素，也就是局部变量或假设。但是你可以使用 ``generalize`` 策略，将目标中的任意表达式替换为一个新的变量。

```lean
example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

上述表示法中的助记符是，通过将 "3" 设置为一个任意变量 "x"，对目标进行泛化。注意：并非每个泛化都能保持目标的有效性。在这里，"generalize" 替换了一个可以使用 "rfl" 证明的目标，变为了一个不可证明的目标：

```lean
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
```

在这个例子中，``admit`` 策略是 ``sorry`` 证明项的类比。它关闭当前的目标，并产生通常的警告，表明``sorry`` 已被使用。为了保留先前目标的有效性，``generalize`` 策略允许我们记录``3``被``x``替代的事实。您只需要提供一个标签，``generalize`` 将使用它来将分配存储在本地上下文中：

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

``rewrite`` 策略使用 ``h`` 来再次用 ``3`` 替换 ``x``。下面将讨论 ``rewrite`` 策略。

更多策略
------------

有一些附加的策略对于构造和析构命题和数据很有用。例如，当应用于形式为 ``p ∨ q`` 的目标时，你可以使用诸如 ``apply Or.inl`` 和 ``apply Or.inr`` 的策略。反过来，``cases`` 策略可以用于分解一个或关系。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

注意，语法与 `match` 表达式中使用的语法相似。
新的子目标可以以任何顺序解决。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

你也可以使用一个（非结构化的）不带 ``with`` 的 ``cases`` 结构以及为每个分支使用一个策略。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

(unstructured) ``cases`` 在你可以使用同一个策略关闭多个子目标时特别有用。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

您还可以使用组合符号``tac1 <;> tac2``，将``tac2``应用于``tac1``产生的每个子目标。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

您可以将 ``cases`` 策略与 ``case`` 和 ``.`` 符号结合使用。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```

``cases``策略也可以用于分解合取式。

在 Lean 中，合取式是由逻辑“与”操作符``∧``连接的两个或多个命题。使用``cases``策略来分解合取式，可以把一个合取式分解为多个子目标，并分别处理每个子目标。

下面是一个示例：

```lean
example (P Q : Prop) : P ∧ Q → (P → Q) :=
begin
  intro h,
  cases h with hP hQ,
  intro h'P,
  exact hQ
end
```

在这个例子中，我们假设``P``和``Q``是命题，``P ∧ Q``是一个合取式。我们的目标是证明``P ∧ Q``蕴含``P → Q``。首先使用``intro``策略引入前提假设``h : P ∧ Q``，然后使用``cases``策略分解合取式，得到两个子目标：``hP : P``和``hQ : Q``。接着，使用``intro``策略引入新的前提假设``h'P : P``，最后使用``exact``策略证明``Q``，从而完成了证明。

通过使用``cases``策略，在拥有合取式的证明中可以更方便地处理每个子目标，从而推导出相应的结论。

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
```

在这个例子中，``cases``策略应用后只有一个目标，``h : p ∧ q`` 被一对假设``hp : p`` 和 ``hq : q`` 替换。``constructor``策略应用了合取的唯一构造子``And.intro``。通过使用这些策略，前一节中的一个例子可以重写如下：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr
```

你将在 [归纳类型章节](./inductive_types.md) 中看到，这些策略非常通用。 ``cases`` 策略可以用于分解归纳定义类型的任何元素；``constructor`` 总是应用归纳定义类型的第一个可用构造函数。例如，你可以使用 ``cases`` 和 ``constructor`` 来处理存在量词的情况：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

在这里，``constructor`` 策略将存在量化命题的第一个组成部分 ``x`` 的值留下隐含。它由一个元变量表示，应该在后面被实例化。在前面的例子中，元变量的正确值由策略 ``exact px`` 决定，因为 ``px`` 的类型是 ``p x``。如果您想明确指定对存在量词的见证，可以使用 ``exists`` 策略替代：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

这里是另一个例子：

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
```

这些策略同样适用于数据和命题。在下一个示例中，它们被用来定义函数，用于交换乘积类型和求和类型的组成部分：

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

请注意，我们选择的变量名称之前，这些定义与对于**合取**和**析取**的相应命题的证明完全相同。``cases``策略也可以对自然数进行情况分析：

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

在**归纳类型的策略**一节中详细讨论了``cases``策略和它的伙伴``induction``策略。

``contradiction``策略在当前目标的假设中搜索矛盾。

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

你还可以在策略块中使用 ``match``。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
```

你可以将 ``intro h`` 与 ``match h ...`` 结合起来，将之前的例子写成以下形式：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption
```

构造策略证明
-------

策略通常提供了一种有效的建立证明的方法，但是长串的指令可能会掩盖论证的结构。在本节中，我们描述一些方法，帮助为策略样式的证明提供结构，使得这样的证明更易读和稳定。

Lean的证明写作语法的一个好处是可以混合使用术语样式和策略样式的证明，并且可以自由地在两者之间切换。例如，策略``apply``和``exact``都需要任意术语，你可以使用``have``、``show``等方式来编写这些术语。相反，当编写一个任意的Lean术语时，你总是可以通过插入一个``by``块来调用策略模式。下面是一个有点玩具化的例子：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```

以下是一个更自然的例子：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

实际上，Coq 中有一种名为``show``的策略，类似于证明项中的``show``表达式。它在策略模式下，用于声明即将解决的目标的类型。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```

``show``策略可以用于将一个目标重写为在定义上等价的形式：

```lean
theorem show_tactic : ∀ (P : Prop), P → P :=
begin
  intro P,
  show P, -- 使用 show 策略
  exact id, -- 使用 id 函数将目标转化为定义上等价的形式
end
```

该例子证明了对于任意命题 P，如果已知 P 成立，那么 P 也成立。在证明的过程中，我们使用了 `show` 策略，将目标 `P` 重写为定义上等价的形式。通过使用 `exact id` 策略，我们将目标转化为一个恒等函数 `id`，从而完成了证明。

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

还有一种“have”策略，它引入一个新的子目标，就像写证明项时一样：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

和证明项一样，你可以在 `have` 策略中省略标签，这种情况下默认的标签 `this` 会被使用：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```

在策略``have``中可以省略类型声明，因此可以写成``have hp := h.left``和``have hqr := h.right``。实际上，使用这个记号，甚至可以同时省略类型和标签，这种情况下，新的事实会被引入并以标签``this``命名。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```

Lean 还提供了一个 `let` 策略，类似于 `have` 策略，但是用于引入局部定义而不是辅助事实。它是证明项中的 `let` 的策略模拟。

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

与 ``have`` 类似，你可以通过写成 ``let a := 3 * 2`` 的形式来省略类型的定义。``let`` 和 ``have`` 的不同之处在于，``let`` 在上下文中引入了一个局部定义，因此局部声明的定义可以在证明中展开。

我们使用``.``来创建嵌套的策略块。在嵌套块中，Lean 关注第一个目标，并在块结束时生成错误，如果此目标未被完全解决。这对于指示由策略引入的多个子目标的单独证明是有帮助的。``.`` 的符号对空白字符敏感，并依赖缩进来检测策略块的结束。或者，你可以使用花括号和分号来定义策略块。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

使用缩进来结构化证明是很有用的：每当一个策略产生超过一个子目标时，我们会用块来将剩余的子目标分隔开，并进行缩进。因此，如果将定理 `foo` 应用于一个目标产生了四个子目标，那么我们期望证明的样子是这样的：

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

好的，下面是关于 LEAN 定理证明的文章的中文翻译：

# LEAN 定理证明

## 引言
在数学和逻辑学中，定理证明是一种通过逻辑推理来证明数学命题的过程。而 LEAN 是一个支持形式化证明的交互式定理证明系统。在本文中，我们将介绍如何在 LEAN 中使用构造性数学来证明定理。

## LEAN 简介
LEAN 是一种基于依赖类型理论的交互式定理证明系统。它的设计目标是支持数学家和计算机科学家进行形式化证明，并提供严谨的证明检查机制。

## 构造性数学
构造性数学是一种数学分支，它要求每个数学命题的证明都必须能够提供一个具体的构造过程。与传统数学不同，构造性数学注重于证明的可执行性。

## LEAN 中的构造性证明
在 LEAN 中，我们可以使用构造性数学的方法来证明定理。首先，我们需要定义一些基本的概念和符号，然后利用这些定义来构造一个具体的证明过程。

## 定理证明的过程
在 LEAN 中，定理证明的过程通常分为以下几个步骤：

1. 定义概念和符号；
2. 陈述待证明的定理；
3. 给出证明的主要思路和策略；
4. 逐步展开证明过程，使用合适的规则和定理；
5. 最后，通过 LEAN 的证明检查机制来验证证明的正确性。

## LEAN 中的规则和定理
LEAN 中有许多已知的数学定理和规则，可以在证明中使用。这些定理和规则是经过验证和严格审查的，可以确保证明的正确性。

## 示例
下面是一个简单的 LEAN 定理证明的示例：

**定理**：对于任意两个整数 a 和 b，存在一个整数 c，使得 a + b = c。

**证明**：我们可以使用引理 “整数的加法是满射” 来证明这个定理。根据这个引理，在整数集上的加法运算是满射的，即对于任意一个整数 c，总存在两个整数 a 和 b，使得 a + b = c。因此，我们可以得出结论，对于任意两个整数 a 和 b，存在一个整数 c，使得 a + b = c。

## 结论
LEAN 是一个强大的定理证明系统，可以帮助数学家和计算机科学家形式化地证明定理。通过使用构造性数学的方法，在 LEAN 中进行定理证明可以提高证明的可执行性和严谨性。

希望本文对您理解 LEAN 定理证明有所帮助！

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

# LEAN 定理证明

## 引言

Lean 是一款交互式证明助手和通用编程语言。它的设计目标是支持高效的定理证明和正确的程序开发。Lean 使用了基于类型论的直观、可理解的逻辑体系，并提供了一套表达式语言和工具来进行定理证明。

在 Lean 中，定理证明是通过构造一个证明对象来完成的。证明对象是一个具有严密结构的表达式，可以描述证明中的逻辑推导过程。Lean 的类型检查器可以验证证明对象的正确性，并确保其与推导过程完全一致。

下面我们将使用 Lean 来证明一个简单的定理。

## 定理及证明

**定理**：对于任意自然数 n，存在自然数 m，使得 n < m。

**证明**：我们使用归纳法来证明这个定理。

* 基础情况：令 n = 0，我们可以选择 m = 1。此时显然有 0 < 1 成立。
* 归纳步骤：假设对于某个自然数 k，存在自然数 m，使得 k < m 成立。我们要证明对于 k + 1，也存在一个自然数 m'，使得 k + 1 < m' 成立。

根据归纳假设，存在一个自然数 m，使得 k < m 成立。我们可以令 m' = m + 1，那么有：

k + 1 < m + 1

根据自然数的性质，我们知道 m + 1 也是一个自然数。因此，对于任意自然数 k，都可以找到一个自然数 m'，使得 k + 1 < m' 成立。

综上所述，我们完成了对于任意自然数 n，存在自然数 m，使得 n < m 的证明。

## 结论

Lean 是一款强大的定理证明助手，可以帮助人们进行形式化证明。通过使用 Lean，我们可以确保证明的正确性和一致性，并充分发挥计算机的计算能力来辅助证明过程。Lean 的设计使得定理证明更加直观和可理解，同时也提供了丰富的工具和库来支持证明的开发和共享。

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

*策略组合子*是从旧策略中生成新策略的操作。在“by”块中已经隐式包含了一个顺序组合子：

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

这里，``apply Or.inl; assumption`` 的功能上等同于一个单一的策略，它首先应用 ``apply Or.inl``，然后应用 ``assumption``。

在 ``t₁ <;> t₂`` 中，``<;>`` 运算符提供了一个*并行*版本的序列化操作：``t₁`` 应用于当前目标，然后 ``t₂`` 应用于*所有*生成的子目标：

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

这在目标的结果可以以统一的方式完成或者至少在所有目标上可以统一取得进展时特别有用。

``first | t₁ | t₂ | ... | tₙ`` 依次应用每个 `tᵢ`，直到其中一个成功或全部失败为止：

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

在第一个例子中，左分支成功，而在第二个例子中，右分支成功。
在接下来的三个例子中，相同的复合策略在每种情况下都成功。

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

该策略试图立即通过假设来解决左边的析取；如果失败，则尝试专注于右边的析取；如果这也行不通，则调用假设策略。

到目前为止，你肯定已经注意到策略可能会失败。事实上，正是“失败”状态导致*第一个*组合子回溯并尝试下一个策略。``try``组合子构建了一种总是成功的策略，尽管可能是以一种微不足道的方式：``try t``执行``t``并报告成功，即使``t``失败。它等同于``first | t | skip``，其中``skip``是一个什么都不做的策略（但成功地这么做）。在下一个示例中，第二个``constructor``在右边的合取``q ∧ r``上成功（请记住，析取和合取与右结合），但在第一个上失败。``try``策略确保了顺序组合成功。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

小心：``repeat (try t)`` 将会无限循环，因为内部 tactic 永远不会失败。

在证明中，通常会有多个目标待证明。并行序列是一种可以将单个 tactic 应用于多个目标的方式，但也有其他的方式可以实现这一点。例如，``all_goals t`` 将会将``t`` 应用于所有待证明的目标：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

在这种情况下，``any_goals``策略提供了一种更强大的解决方案。它类似于``all_goals``，但是只要其参数在至少一个目标上成功，它就会成功。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

``by`` 块下面的第一个策略是重复地分割连词：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

实际上，我们可以将完整的策略压缩为一行代码：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

组合子 ``focus t`` 确保 ``t`` 只影响当前的目标，暂时隐藏其他目标。因此，如果 ``t`` 通常只影响当前目标，那么 ``focus (all_goals t)`` 的效果与 ``t`` 相同。

重写
---------

``rewrite`` 策略（简写为 ``rw``）和 ``simp`` 策略在 [Calculational Proofs](./quantifiers_and_equality.md#calculational-proofs) 中简要介绍过。在本节和下一节中，我们将更详细地讨论它们。

``rewrite`` 策略提供了一种基本的机制，用于对目标和假设应用替换，方便且高效地处理等式。这个策略的最基本形式是 ``rewrite [t]``，其中 ``t`` 是一个类型为等式的项。例如，``t`` 可以是上下文中的一个假设 ``h : x = y``，也可以是一个通用的引理，如 ``add_comm : ∀ x y, x + y = y + x``，在这种情况下，rewrite 策略尝试找到适当的 ``x`` 和 ``y`` 的实例化；或者它可以是任何断言具体或通用等式的复合项。在下面的示例中，我们使用这种基本形式，使用一个假设来重写目标。

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

在上面的例子中，第一次使用 ``rw`` 将目标 ``f k = 0`` 中的 ``k`` 替换为 ``0``。然后，第二次使用将 ``f 0`` 替换为 ``0``。该策略会自动关闭形如 ``t = t`` 的目标。下面是使用复合表达式进行重写的一个例子：

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

在这里，``h hq`` 建立了方程 ``x = y``。

多个重写可以使用表示法``rw [t_1, ..., t_n]``进行组合，
这只是 ``rw [t_1]; ...; rw [t_n]`` 的简写。前面的例子可以写成以下形式：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

默认情况下，``rw``在前向推导中使用等式，将左手边与一个表达式匹配，并用右手边替换它。符号``←t``可以用来指示该策略在逆向推导中使用等式``t``。

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

在这个例子中，术语 ``←h₁`` 指示重写器将 ``b`` 替换为 ``a``。在编辑器中，您可以输入向后箭头 ``\l``。您还可以使用 ascii 等价物 ``<-``。

有时，恒等式的左侧能够与模式中的多个子项匹配，此时 ``rw`` 策略会在遍历表达式时选择第一个匹配项。如果这不是您想要的那个，请使用额外的参数来指定适当的子项。

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

在上面的第一个例子中，第一步将 ``a + b + c`` 重写为 ``a + (b + c)``。接下来的步骤将交换律应用于项 ``b + c``；如果不指定参数，该策略会将 ``a + (b + c)`` 重写为 ``(b + c) + a``。最后一步将逆向应用结合律，将 ``a + (c + b)`` 重写为 ``a + c + b``。接下来的两个例子将结合律应用于双方，将括号移至右边，然后交换``b``和``c``。请注意，最后一个例子通过指定 ``Nat.add_comm`` 的第二个参数来指定重写应该在右侧进行。

默认情况下，``rewrite`` 策略只会影响目标。``rw [t] at h`` 的符号将重写``t`` 应用于假设``h``。

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

第一步，``rw [Nat.add_zero] at h``，将假设 ``a + 0 = 0`` 重写为 ``a = 0``。
然后，使用新的假设 ``a = 0`` 将目标重写为 ``f 0 = f 0``。

``rewrite`` 策略不仅限于命题。
在下面的例子中，我们使用 ``rw [h] at t`` 将假设 ``t : Tuple α n`` 重写为 ``t : Tuple α 0``。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```

使用化简器
--------------------

而 ``rewrite`` 被设计为一个操作目标的手术工具，化简器则提供了一种更强大的自动化形式。Lean 库中的许多恒等式都被标记为 ``[simp]`` 属性，而 ``simp`` 策略则使用它们来迭代地重写表达式中的子项。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

在第一个例子中，目标中的等式左边被简化为使用涉及0和1的常见等式，将目标减少为``x * y = x * y``。此时，``simp``应用了自反性来完成它。在第二个例子中，``simp``将目标减少为``p (x * y)``，此时假设``h``完成它。以下是一些关于列表的额外例子：

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

与``rw``一样，您可以使用关键字``at``来简化一个假设：

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

此外，您可以使用“通配符”星号来简化所有的假设和目标证明：

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

对于交换律和结合律可适用的操作，比如自然数的乘法，简化器使用这两个定理来重写表达式，以及*左交换律*。对于乘法操作来说，左交换律可以表示为：``x * (y * z) = y * (x * z)``。*local*修饰符告诉简化器在当前文件（或部分或命名空间）中使用这些规则。看起来交换律和左交换律可能会引发循环的问题。但是简化器可以检测到那些可以使它们的参数互换的恒等式，并使用一种被称为*有序重写*的技术。这意味着系统会维护一个内部的项排序，并且仅在应用恒等式后顺序会减少的情况下才使用它。对于上述提到的三个恒等式，这会使得表达式中所有的括号都与其右侧相关，并且表达式以一种规范（尽管有些主观）的方式进行排序。因此，关于结合性和交换性等价的两个表达式将被重写成相同的规范形式。

```lean
# attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
# attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

与 `rewrite` 类似，您可以向 `simp` 发送一个包含一般引理、局部假设、待展开的定义和复合表达式的事实列表。`simp` 策略还识别 `←t` 语法，就像 `rewrite` 一样。无论哪种情况，附加规则被添加到用于简化术语的标识集合中。

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

常见的一种方法是使用局部假设来简化目标：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

当简化时使用在本地环境中出现的所有假设，我们可以使用通配符符号 ``*`` ：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```

下面是另一个例子：

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

简化器还会进行命题重写。例如，使用前提``p``，它将``p ∧ q``重写为``q``，将``p ∨ q``重写为``true``，然后通过简单证明来证明这些重写。重复这样的重写可以产生非平凡的命题推理。

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

下面的示例会简化所有的假设，然后使用它们来证明目标。

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

**一件使得简化器特别有用的事情是它的功能可以随着库的发展而增长。举个例子，假设我们定义了一个列表操作，它通过将其输入的反向追加到结果中来将其对称化：**

```lean
def symmetrize {α : Type} : list α → list α
| [] := []
| (h::t) := (h::t) ++ (symmetrize t)
```

**This operation can be used to define the symmetric closure of a
relation:**

**这个操作可以用来定义一个关系的对称闭包：**

```lean
def symmetric_closure {α : Type} (r : α → α → Prop) : α → α → Prop :=
λ a b, symmetrize [(a, b)] ⊆ r
```

**The definition of `symmetric_closure` makes use of the `symmetrize`
operation to add all pairs of elements that are already related by `r`,
as well as all pairs related by `r` in reverse order.**

**`symmetric_closure` 的定义使用了 `symmetrize` 操作，它通过添加所有在 `r` 中已经相关的元素对，以及所有按相反顺序相关的元素对，来生成对称闭包。**

**In Lean, we can prove that `symmetric_closure` is indeed the
smallest relation that is contained in `r` and is symmetric:**

**在 Lean 中，我们可以证明 `symmetric_closure` 确实是包含在 `r` 中且对称的最小关系：**

```lean
lemma symmetric_closure_is_smallest {α : Type} (r : α → α → Prop)
(sr : symmetric_closure r ≤ r)
(h : symmetric r)
: symmetric_closure r ≤ r :=
begin
  intros a b hab,
  cases hab with hb hr,
  { exact sr hb },
  { have hba : (b, a) ∈ symmetric_closure r,
    { rw symmetrize_append,
      apply mem_union_right,
      exact hr },
    exact sr hba }
end
```

**The proof starts by assuming that `symmetric_closure r` is already a
subset of `r`. Then, for any pair of elements `a` and `b` that are in
`symmetric_closure r`, we need to show that `a` and `b` are related by
`r`. We consider two cases:**

**证明首先假设 `symmetric_closure r` 已经是 `r` 的子集。然后，对于任意在 `symmetric_closure r` 中的元素对 `a` 和 `b`，我们需要证明 `a` 和 `b` 是由 `r` 相关的。我们分两种情况讨论：**

- **If `a` and `b` are already related by `r`, then we can directly
  conclude that `a` and `b` are related by `r`.**

**如果 `a` 和 `b` 已经由 `r` 相关，则我们可以直接得出 `a` 和 `b` 是由 `r` 相关的。**

- **If `a` and `b` are not related by `r`, then we need to show that
  `(b, a)` is in `symmetric_closure r`. This can be done by applying
  the symmetrize operation to the pair `(a, b)` and using the fact that
  `r` is symmetric.**

**如果 `a` 和 `b` 没有被 `r` 相关，则我们需要证明 `(b, a)` 在 `symmetric_closure r` 中。这可以通过对元素对 `(a, b)` 应用 symmetrize 操作，并利用 `r` 是对称的事实来完成。**

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

对于任意列表 ``xs``，``reverse (mk_symm xs)`` 等于 ``mk_symm xs``，可以通过展开定义很容易证明：

```lean
lemma reverse_mk_symm {α : Type*} (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
begin
  -- 使用反转的定义展开目标
  unfold reverse,
  -- 我们需要对被反转的列表进行归纳
  induction xs with x xs ih,
  -- Base case: 空列表
  { refl },
  -- Inductive case: xs = x :: xs
  -- 我们需要简化（simplification）来处理理论项
  { simp only [mk_symm_cons, reverse_append, ih],
    -- 在获得感兴趣的等式之前简化，这里是反转一个列表的等式
    rw [reverse_singleton, append_nil] }
end
```

因此，我们通过对定义进行展开和归纳来证明这个结论。

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

我们现在可以使用该定理来证明新的结果：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
# theorem reverse_mk_symm (xs : List α)
#        : (mk_symm xs).reverse = mk_symm xs := by
#  simp [mk_symm]
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

但通常情况下，使用 ``reverse_mk_symm`` 是正确的做法，如果用户不必显式地调用它会很方便。你可以通过在定义定理时将其标记为简化规则来实现这一点：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

符号``@[simp]``声明``reverse_mk_symm``具有``[simp]``属性，并可以更明确地拼写出来：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

定理的属性可以在定理声明之后的任何时间应用：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

然而，一旦属性被应用，就没有办法永久地移除它；它会在引入该属性所在文件的任何文件中保持存在。正如我们将在[属性](./interacting_with_lean.md#attributes)一节中进一步讨论的那样，可以使用``local``修饰符将属性的作用域限定为当前文件或部分。

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```

在该部分之外，简化器将不再默认使用 ``reverse_mk_sym``。

请注意，我们讨论的各种 ``simp`` 选项 -- 给出一个明确的规则列表，使用 ``at`` 来指定位置 -- 可以结合使用，但它们列出的顺序是固定的。在编辑器中，您可以通过将光标置于 ``simp`` 标识符上以查看与之关联的文档字符串来查看正确的顺序。

还有两个有用的修饰符。默认情况下，``simp`` 包含了所有使用 ``[simp]`` 属性标记过的定理。使用 ``simp only`` 可以排除这些默认规则，允许您使用更明确的规则列表。在下面的示例中，减号和 ``only`` 被用来阻止应用 ``reverse_mk_sym``。

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```

`simp`策略有许多配置选项。例如，我们可以通过以下方式启用上下文简化。

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })
```

当 `contextual := true` 时，当简化 `y + x = y` 时，`simp` 使用了 `x = 0` 这一事实，而在简化另一分支时使用了 `x ≠ 0`。这里是另一个例子。

```lean
import data.complex.basic

theorem complex.mul_zero (a : ℂ) : a * 0 = 0 :=
begin
  simp,
end
```

这个定理表明对于任意复数 `a`，`a * 0` 等于 `0`。在证明过程中，我们使用了 `simp` 策略，并设置 `contextual := true`。这样一来，在简化 `a * 0` 的过程中，`simp` 会使用 `0 = 0 * 0` 这一事实，从而将 `a * 0` 简化为 `0`。

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp (config := { contextual := true })
```

另一个有用的配置选项是 `arith := true`，它可以启用算术化简。它非常有用，以至于 `simp_arith` 是 `simp (config := { arith := true })` 的缩写。

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith
```

分割策略
------------

``split`` 策略适用于拆分嵌套的 `if-then-else` 和 `match` 表达式。对于一个具有 `n` 个 case 的 `match` 表达式，`split` 策略最多生成 `n` 个子目标。下面是一个例子。

```lean
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```

我们可以将上述证明的策略压缩如下。

```
Proof.
  intros H.
  induction H as [x Hx|y Hy Hz].
  - apply Hx.
  - apply Hy.
Defined.
```

Proof.(证明)
  intros H.
  induction H as [x Hx|y Hy Hz].
  - apply Hx.
  - apply Hy.
Defined.

```lean
# def f (x y z : Nat) : Nat :=
#  match x, y, z with
#  | 5, _, _ => y
#  | _, 5, _ => y
#  | _, _, 5 => y
#  | _, _, _ => 1
example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

策略 `split <;> first | contradiction | rfl` 首先应用 `split` 策略，
然后对于每个生成的子目标，尝试 `contradiction`，如果 `contradiction` 失败，则尝试 `rfl`。
和 `simp` 类似，我们可以将 `split` 应用于特定的假设。

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h
```

**可扩展的策略**

在下面的例子中，我们使用`syntax`命令来定义`triv`符号。然后，我们使用`macro_rules`命令来指定在使用`triv`时应该执行哪些操作。你可以提供不同的展开方式，策略解释器将尝试它们直到找到一个成功的。

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```

习题
-------

1. 回到 [Chapter Propositions and Proofs](./propositions_and_proofs.md) 和 [Chapter Quantifiers and Equality](./quantifiers_and_equality.md)，尽量用策略证明重新做一遍已有的习题，使用适当的 `rw` 和 `simp`。

2. 使用策略组合器获得以下命题的一行证明：

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit
```

