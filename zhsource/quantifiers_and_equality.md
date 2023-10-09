全称量化
------------------------

注意，如果 ``α`` 是任意类型，我们可以将 ``α`` 上的一元谓词 ``p`` 表示为类型为 ``α → Prop`` 的对象。在这种情况下，给定 ``x:α``，``p x`` 表示 ``p`` 对于 ``x`` 成立的断言。类似地，对象 ``r ：α → α → Prop`` 表示 ``α`` 上的二元关系：给定 ``x y : α``，``r x y`` 表示 ``x`` 和 ``y`` 有关系的断言。

全称量化符号 ``∀ x : α, p x`` 被认为表示了“对于每个 ``x : α`` ， ``p x`` 成立”的断言。和命题联结词一样，在自然推理系统中，“对于所有”受到引入规则和消除规则的制约。非正式地说，引入规则如下：

> 在一个假设为 ``x : α`` 的上下文中给定 ``p x`` 的证明，我们可以得到一个证明 ``∀ x : α, p x``。

消除规则如下：

> 给定一个证明 ``∀ x : α, p x`` 和任意项 ``t : α``，我们可以得到一个证明 ``p t``。

和蕴含的情况相同，类型为命题的项来进行解释。回想一下依赖箭头类型的引入和消除规则：

> 给定类型为 ``β x`` 的项 ``t``，在一个假设为 ``x : α`` 的上下文中我们有 ``(fun x : α => t) : (x : α) → β x``。

消除规则如下：

> 给定一个类型为 ``(x : α) → β x`` 的项 ``s`` 和任意项 ``t : α``，我们有 ``s t : β t``。

在 ``p x`` 的类型为 ``Prop`` 的情况下，如果我们将 ``(x : α) → β x`` 替换为 ``∀ x : α, p x``，我们可以将这些规则解释为关于全称量化的构建证明的正确规则。
因此，Constructions计算将依赖箭头类型与forall表达式等同起来。如果 ``p`` 是任何表达式，那么 ``∀ x : α, p`` 不过是 ``(x : α) → p`` 的别名，前者在 ``p`` 是命题的情况下比后者更加自然。通常情况下，表达式 ``p`` 会依赖于 ``x : α``。回想一下，在普通函数空间的情况下，我们可以将 ``α → β`` 解释为 ``(x : α) → β`` 的特殊情况，其中 ``β`` 不依赖于 ``x``。类似地，我们可以将命题之间的蕴含关系 ``p → q`` 视为 ``∀ x : p, q`` 的特殊情况，其中表达式 ``q`` 不依赖于 ``x``。

下面是一个展示命题即类型对应关系如何实践的例子。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

作为一项符号约定，我们将全称量词的作用范围设定为最宽，因此需要用括号将量词限制在上述示例的前提中。证明 ``∀ y : α, p y`` 的经典方式是取一个任意的 ``y``，并证明 ``p y``。这是引入规则。现在，假设 ``h`` 的类型是 ``∀ x : α, p x ∧ q x``，那么表达式 ``h y`` 的类型是 ``p y ∧ q y``。这是消去规则。取左合取项即得到所需结论，即 ``p y``。

请记住，只要变量的绑定不同，表达式即被认为是等价的。因此，例如，在假设和结论中可以使用相同的变量 ``x``，并在证明中用不同的变量 ``z`` 实例化它：

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

另一个例子是我们如何表达一个关系 `r` 是可传递的：

```lean
def transitive {α : Type} (r : α → α → Prop) : Prop :=
∀ (a b c : α), r a b → r b c → r a c
```

这里，我们定义了一个函数 `transitive`，它接受一个类型为 `α` 的参数，以及一个从 `α` 到 `α` 到命题的关系 `r`。函数的类型为 `Prop`，即表示命题的类型。在函数体内，我们使用了一个全称量化的命题，即对于任意的 `a`、`b`、`c`，如果 `r a b` 和 `r b c` 成立，那么 `r a c` 也成立。这个定义就表达了关系 `r` 是可传递的这一事实。

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
```

考虑这里发生了什么。当我们使用值 ``a b c`` 实例化 ``trans_r`` 时，我们得到了一个证明，即 ``r a b → r b c → r a c``。将其应用于“假设”``hab : r a b``，我们得到了一个蕴含的证明 ``r b c → r a c``。最后，将其应用于假设``hbc``，我们得到了一个结论的证明``r a c``。

在这种情况下，如果从 ``hab hbc`` 可以推断出 ``a b c``，那么提供这些参数可能会很繁琐。因此，通常会将这些参数设为隐式的：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

**好处**是我们可以简单地写``trans_r hab hbc``来证明``r a c``。缺点是Lean没有足够的信息来推断表达式``trans_r``和``trans_r hab``的参数类型。第一个``#check``命令的输出是``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``，表示在这种情况下隐式参数未指定。

以下是如何使用等价关系进行基本推理的示例：

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

为了熟悉使用全称量词，你应该尝试一下这节末尾的一些练习题。

正是依赖箭头类型的类型规则，尤其是普遍量化符号，使得 ``Prop`` 与其他类型有所区别。假设我们有 ``α : Sort i`` 和 ``β : Sort j``，其中表达式 ``β`` 可能依赖于变量 ``x : α``。然后 ``(x : α) → β`` 是 ``Sort (imax i j)`` 的一个元素，其中 ``imax i j`` 是如果 ``j`` 不为0，则为 ``i`` 和 ``j`` 的最大值，否则为0。

思路如下。如果 ``j`` 不是 ``0``，那么 ``(x : α) → β`` 是 ``Sort (max i j)`` 的一个元素。换句话说，从 ``α`` 到 ``β`` 的依赖函数的类型 "存在" 在索引为 ``i`` 和 ``j`` 的最大值的宇宙中。然而，假设 ``β`` 是 ``Sort 0``，即属于 ``Prop`` 的一个元素。在这种情况下，无论 ``α`` 生活在哪种类型宇宙中， ``(x : α) → β`` 也是 ``Sort 0`` 的一个元素。换句话说，如果 ``β`` 是依赖于 ``α`` 的命题，那么 ``∀ x : α, β`` 再次是一个命题。这反映了将 ``Prop`` 解释为命题类型而不是数据类型的含义，并且正是这使得 ``Prop`` *不可谓的*。

术语 "头等预测" 起源于二十世纪转折时期的基础研究，当时像庞加莱和罗素这样的逻辑学家归咎于集合论悖论，原因是当我们通过量化集合来定义属性时，就出现了 "恶性循环"。请注意，如果 ``α`` 是任意类型，我们可以构造类型 ``α → Prop``，表示所有关于 ``α`` 的谓词的类型（``α`` 的 "幂类型"）。``Prop`` 的不可预测性意味着我们可以形成量化整个 ``α → Prop`` 的命题。特别地，我们可以通过量化所有关于 ``α`` 的谓词来定义关于 ``α`` 的谓词。
关于 Lean 定理证明
==========

在 Lean 的定理证明库中，*等式（equality）* 是其中的一个最基本的关系。在 [归纳类型（Inductive Types）章节](inductive_types.md) 中，我们将解释 *等式是如何从 Lean 逻辑框架的基本元素中定义出来的。在此期间，我们将解释如何使用它。

当然，等式的一个基本性质就是它是一个等价关系：

```lean
#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ?m.2 = ?m.3 → ?m.3 = ?m.2
#check Eq.trans   -- ?m.2 = ?m.3 → ?m.3 = ?m.4 → ?m.2 = ?m.4
```

我们可以通过告诉 Lean 不插入隐式参数（在这里显示为元变量）来使输出更易读。

```lean
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

LEᴀɴ θᴇᴏʀᴇᴍ-7: 给定一个类型``A``和``x, y : A``，表达式``x = y``（即x和y相等）类型为``Pro p``。

证明：通过引入类型 A，我们可以实例化上述引理以证明它对于任何类型 A 是成立的。假设``A``是一个类型，并且``x, y : A``是 A 上的任意两个元素。我们的目标是证明``x = y``是一个命题。

根据上述引理的定义，我们需要实例化它的类型为``Type (max u v)``，其中 u 和 v 是``x``和``y``所在的宇宙的级别。在此证明中，我们将使用它们的级别作为我们实例化的宇宙 u 和 v 的值。

此外，我们还需要为此引理提供其他的参数，例如``x``和``y``的类型，即``A``。此外，我们还需要提供一个以证明``x = y``的证据构造函数。

在这种情况下，由于我们没有提供任何特定的``x``和``y``的值，我们不能使用等价关系（``=``）的构造函数。相反，我们只需要证明在任何情况下，当``x``和``y``都被视为命题时，它们是相等的。

因此，我们可以确定``x = y``的类型为``Prop``，它是``Type``的一个子类型，用于表示命题。通过此推理，我们完成了对``x = y``是一个命题的证明。

因此，我们可以得出结论：对于任何类型``A``和``x, y : A``，表达式``x = y``是一个命题。

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

我们还可以使用投影符号表示：

```lean
# variable (α : Type) (a b c d : α)
# variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd
```

自反比它看起来更强大。回想一下，构造演算中的项具有计算解释，并且逻辑框架将具有共同还原的项视为相同。因此，一些非平凡的等式可以通过自反来证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

这个框架的这个特性非常重要，因此库为``Eq.refl _``定义了一个记号``rfl``：

```lean
# variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

然而，等式远不止是一种等价关系。它具有重要的性质，即每个命题都尊重等价关系，也就是说我们可以在不改变真值的情况下替换相等的表达式。换句话说，给定 ``h1: a = b`` 和 ``h2: p a``，我们可以使用替换操作``Eq.subst h1 h2`` 构建一个证明 ``p b``。

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

第二个表达式中的三角形是在 ``Eq.subst`` 和 ``Eq.symm`` 之上构建的宏，你可以通过键入 ``\t`` 来输入它。

规则 ``Eq.subst`` 用于定义以下辅助规则，它们执行更明确的替换。它们旨在处理可应用项，即形如 ``s t`` 的项。具体来说，``congrArg`` 可以用于替换参数，``congrFun`` 可以用于替换被应用的项，``congr`` 可以一次替换两者。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Lean 的库中包含大量常见的恒等式，比如这些：

* **对称律（Symmetry）**：对于任意两个对象 P 和 Q，如果 P 等于 Q，那么 Q 也等于 P。
* **传递律（Transitivity）**：对于任意三个对象 P、Q 和 R，如果 P 等于 Q，且 Q 等于 R，那么 P 等于 R。
* **自反性（Reflexivity）**：对于任意对象 P，P 等于 P。
* **加法的单位元（Addition Identity）**：对于任意对象 P，P 加 0 等于 P。
* **加法的逆元（Addition Inverse）**：对于任意对象 P，存在一个对象 Q，使得 P 加 Q 等于 0。
* **乘法的单位元（Multiplication Identity）**：对于任意对象 P，P 乘 1 等于 P。
* **乘法的逆元（Multiplication Inverse）**：对于任意对象 P，如果 P 不等于 0，那么存在一个对象 Q，使得 P 乘 Q 等于 1。
* **乘法的分配律（Multiplication Distributivity）**：对于任意三个对象 P、Q 和 R，(P 加 Q) 乘 R 等于 P 乘 R 加 Q 乘 R。

这些恒等式是数学中经常使用的基本原理，在 Lean 中被用来构建更复杂的证明。

```lean
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

注意，``Nat.mul_add`` 和 ``Nat.add_mul`` 是 ``Nat.left_distrib`` 和 ``Nat.right_distrib`` 的另外两个名字。上述性质都是针对自然数（类型为 ``Nat``）而言的。

这里是一个在自然数中使用替换、结合律和分配律进行计算的例子。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

注意到``Eq.subst``的第二个隐式参数，它提供了进行替换的上下文，类型为``α → Prop``。因此，推断此谓词需要一个*高阶一致性*实例。在完整的一般情况下，确定一个高阶一致性是否存在是不可判定的，而Lean在最佳情况下只能对这个问题提供不完美和近似的解决方案。因此，``Eq.subst``并不总能做到您希望的那样。宏``h ▸ e``使用了更有效的启发式方法来计算这个隐式参数，在应用``Eq.subst``失败的情况下通常会成功。

由于等式推理是如此常见和重要，Lean提供了一些机制来更有效地进行推理。下一节提供了一些语法，使您能够以更自然和清晰的方式编写计算证明。但是，更重要的是，等式推理还得到了术语重写器、简化器和其他类型的自动化支持。术语重写器和简化器在下一节中简要介绍，然后在下一章中详细描述。

计算证明
--------------------

计算证明就是一个由中间结果构成的链条，这些中间结果可以通过基本原理（如等式的传递性）进行组合。在Lean中，计算证明以关键字``calc``开始，具有以下语法：

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

注意，`calc` 关系的所有缩进都相同。每个 `<proof>_i` 都是 `<expr>_{i-1} op_i <expr>_i` 的一个证明。

我们还可以在第一个关系（紧跟着 `<expr>_0` 的右边）中使用 `_`，这有助于对齐关系/证明对的序列：

```
calc <expr>_0 
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

这里是一个例子：

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

这种证明方法在与``simp``和``rewrite``策略结合使用时效果最好，这些策略将在下一章中详细讨论。例如，使用``rw``缩写为rewrite，上面的证明可以写作如下：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

实际上，``rw`` 策略使用给定的等式（可以是假设、定理名或复杂的项）来“重写”目标。如果这样做将目标缩减为恒等式 ``t = t``，则该策略将应用自反性来证明它。

重写可以按顺序应用，因此上述证明可以简化为以下形式：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

甚至这样：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

相反，``simp``策略通过重复应用给定的等式，以任意顺序和任何适用的位置，重写目标。它还使用了之前在系统中声明过的其他规则，并明智地应用交换律以避免循环。因此，我们可以通过以下方式证明该定理：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

我们将在下一章讨论关于 ``rw`` 和 ``simp`` 的变化。

``calc`` 命令可以配置成支持某种形式的可传递性的任意关系。甚至可以组合不同的关系。

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

您可以通过添加 `Trans` 类型类的新实例来，“教” `calc` 新的传递性定理。类型类的介绍稍后会给出，但下面的小例子演示了如何使用新的 `Trans` 实例来扩展 `calc` 表示法。

```Lean
class Trans (α : Type) : Type :=
  (trans : α → α → α)

instance add_trans : Trans nat :=
  ⟨λ a b, a + b⟩

instance mul_trans : Trans nat :=
  ⟨λ a b, a * b⟩

instance concat_trans : Trans string :=
  ⟨λ a b, a ++ b⟩

def calc {α : Type} [Trans α] := α

notation `⟦` a `⟧` := calc.eval a

infixl:1 "×" => Trans.trans
infixl:0 "+" => Trans.trans

def add_example : nat :=
  ⟦2 + 3 * 4⟧

def mul_example : nat :=
  ⟦2 × 3 + 4⟧

def concat_example : string :=
  ⟦"Hello, " ++ "World!"⟧

#reduce add_example
#reduce mul_example
#reduce concat_example
```

上述代码通过为 `nat` 和 `string` 类型分别创建了 `Trans` 实例 `add_trans`、`mul_trans` 和 `concat_trans`。这些实例定义了 `trans` 方法，该方法将两个值合并为一个值。

然后，我们定义了 `calc` 函数，该函数接受一个类型参数 `α` 和一个 `Trans` 实例。该函数通过 `α` 和 `Trans` 实例来确定要使用的运算符。

接下来，我们定义了 `add_example`、`mul_example` 和 `concat_example` 三个示例，它们使用了 `calc` 表示法来计算不同类型的表达式。

最后，我们使用 `#reduce` 命令分别计算了这三个示例。

```lean
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..
```

上面的例子还清楚地表明，即使您没有关于您的关系的中缀表示法，也可以使用`calc`。最后，我们注意到上面的例子中的垂直线符号`∣`是Unicode版本的。我们使用Unicode来确保不重载`match .. with`表达式中使用的ASCII字符`|`。

使用`calc`，我们可以以一种更自然和明了的方式编写上一节中的证明。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
```

这里值得考虑使用一种叫 `calc` 的替代符号表示法。当第一个表达式占据了这么多空间时，在第一个关系中使用 `_` 自然会对齐所有关系：

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
```

这里 ``Nat.add_assoc`` 前面的箭头告诉 rewrite 在相反的方向上使用这个等式（你可以用 ``\l`` 输入它或者用 ASCII 码的等价表示 ``<-``）。如果我们追求简洁， ``rw`` 和 ``simp`` 都可以单独完成这个任务：

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

存在量化器
----------

最后，考虑存在量化器，可以写作 ``exists x : α, p x`` 或者 ``∃ x : α, p x``。实际上，这两个版本都是更冗长表达式的便利缩写，即 ``Exists (fun x : α => p x)``，在 Lean 的库中已经定义好了。

正如你现在所期望的那样，这个库包含引入规则和消除规则。引入规则很直接：要证明 ``∃ x : α, p x``，只需提供一个合适的项 ``t`` 和一个证明 ``p t``。以下是一些例子：

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro
```

当上下文中的类型清晰时，我们可以使用匿名构造符号 ``⟨t, h⟩`` 来表示 ``Exists.intro t h``。

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

注意，``Exists.intro``具有隐式参数：Lean必须推断出结论中的谓词``p：α → Prop``，即``∃x，p x``。这不是一个简单的事情。例如，如果我们有``hg：g 0 0 = 0``并写``Exists.intro 0 hg``，则谓词``p``可能有很多可能的值，对应于定理``∃ x，g x x = x``、``∃ x，g x x = 0``、``∃ x，g x 0 = x``等。Lean使用上下文推断哪一个是合适的。以下示例说明了此情况，在其中我们将选项``pp.explicit``设置为true，以要求Lean的漂亮打印机显示隐式参数。

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
```

我们可以将 ``Exists.intro`` 视为一种信息隐藏的操作，因为它隐藏了对断言主体的见证。 存在消去规则 ``Exists.elim`` 执行相反的操作。 它允许我们从 ``∃ x : α，p x`` 来证明一个命题 ``q``，通过展示对于任意值 ``w``，``q`` 从 ``p w`` 推导出来。 粗略地说，由于我们知道存在满足 ``p x`` 的 ``x``，我们可以给它一个名字，比如 ``w``。 如果 ``q`` 不提及 ``w``，那么展示 ``q`` 从 ``p w`` 推导出来等价于展示 ``q`` 从任何这样的 ``x`` 的存在推导出来。 这是一个例子：

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

对于存在消去规则，与“或”消去法进行比较可能会有所帮助：命题“∃ x : α, p x”可以被看作命题“p a”的一个大的析取，其中“a”遍历整个“α”。请注意，匿名构造符号“⟨w, hw.right, hw.left⟩”是一个嵌套构造应用的缩写；我们同样可以写作“⟨w, ⟨hw.right, hw.left⟩⟩”。

注意，存在命题与Σ类型非常相似，正如在依赖类型部分中所描述的那样。区别在于给定“a : α”和“h : p a”，术语“Exists.intro a h”的类型为“(∃ x : α, p x) : Prop”，而“Sigma.mk a h”的类型为“(Σ x : α, p x) : Type”。∃和Σ之间的相似性是柯里-霍华德同构的另一个例子。

Lean提供了一种更方便的方法来通过“match”表达式消去存在量词：

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

``match``表达式是Lean函数定义系统的一部分，它提供了定义复杂函数的便捷且表达力强的方法。再次地，正是Curry-Howard同构使得我们能够利用这个机制来编写证明。``match``语句将存在断言“解构”为组件``w``和``hw``，然后可以在语句的主体中使用它们来证明命题。我们可以为匹配中使用的类型添加注释以增加清晰度：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

我们甚至可以使用 match 语句同时分解合取式：

```lean
variables P Q R : Prop

example (h : P ∧ Q ∧ R) : P ∧ Q :=
match h with ⟨hp, hq, _⟩ :=
  ⟨hp, hq⟩
end
```

在这个例子中，我们假设了一个命题 `P`、`Q` 和 `R` 构成的合取式 `h`，我们想要证明 `P ∧ Q`。我们使用 match 语句来分解合取式 `h`，并将分解得到的 `P` 和 `Q` 分别命名为 `hp` 和 `hq`。然后我们使用构造子 `⟨⟩` 来重新构建合取式，得到证明 `⟨hp, hq⟩`。最后我们使用 match 语句的结束符号 `end` 表示 match 语句结束。由于我们只关心 `P` 和 `Q`，所以我们对 `R` 不做任何处理。因此，我们成功地将合取式 `h` 分解为 `P` 和 `Q`。

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

Lean 还提供了一种模式匹配的 ``let`` 表达式：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

这实质上只是上述 `match` 构造的一种替代表示方法。Lean 甚至允许我们在 `fun` 表达式中使用隐式 `match`：

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

我们将在 [归纳与递归章节](./induction_and_recursion.md) 中看到，所有这些变体都是更一般的模式匹配结构的实例。

在下面的示例中，我们将 ``is_even a`` 定义为 ``∃ b, a = 2 * b``，然后我们证明两个偶数的和仍然是一个偶数。

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
```

使用本章描述的各种工具——匹配语句、匿名构造函数和“rewrite”策略，我们可以将此证明简洁地写成如下形式：

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

正如构造上的“或”比经典上的“或”更强，构造上的“存在”也比经典上的“存在”更强。举个例子，以下蕴含关系需要经典的推理，因为从构造的角度来看，知道并非每个“x”满足“¬p”并不等同于找到一个特定的“x”满足“p”。

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

以下是一些涉及存在量词的常见等式。在下面的练习中，我们鼓励您尽可能证明更多的等式。我们也让您自行确定哪些是非构造性的，因此需要某种形式的古典推理。

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

请注意，第二个示例和最后两个示例需要作出假设：至少存在一个类型为 ``α`` 的元素 ``a``。

以下是两个较难示例的解决方案：

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

关于证明语言的更多内容
-------------------------

我们已经看到，“fun”、“have”和“show”等关键字使得我们可以编写形式化证明项，这些证明项与非形式化的数学证明结构相似。在本节中，我们将讨论一些通常方便的证明语言的其他特性。

首先，我们可以使用匿名的“have”表达式引入辅助目标，而无需为其添加标签。我们可以使用关键字“this”引用以这种方式引入的最后一个表达式：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

通常证明会从一个事实转移到另一个事实，这样可以有效地消除大量标签的混乱。

当目标可以被推断出来时，我们还可以要求 Lean 通过写入“``by assumption``”来填充证明：

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

这样告诉 Lean 使用 ``assumption`` 策略，该策略通过在局部上下文中找到合适的假设来证明目标。我们将在下一章中更多地了解 ``assumption`` 策略。

我们也可以要求 Lean 在证明中填入 ``‹p›``，其中 ``p`` 是我们想要 Lean 在上下文中找到的命题的证明。你可以使用 ``\f<`` 和 ``\f>`` 输入这些引号。字母 "f" 代表 "French"，因为这些 unicode 符号也可以用作法语引号。实际上，该符号在 Lean 中的表示方式如下：

```lean
notation "‹" p "›" => show p by assumption
```

这种方法比使用“假设”的方法更加稳健，因为需要推断的假设的类型是明确给出的。它使得证明更容易阅读。下面是一个更详细的示例：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

请记住，在这种情况下你可以使用法语引号来引用“任何”上下文中的内容，不仅仅限于匿名引入的事物。它的使用也不限于命题，尽管将其用于数据有些奇怪：

```lean
example (n : Nat) : Nat := ‹Nat›
```

以后我们将展示如何使用 Lean 的宏系统扩展证明语言。

练习
------

1. 证明以下等价关系：

```lean
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```

你也应该尝试理解为什么在最后一个例子中无法推导出反向蕴含。

2. 当一个组成公式的部分不依赖于量化变量时，通常可以将其从普遍量词外部提取出来。尝试证明以下命题（第二个命题的一个方向需要使用经典逻辑）：

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. 考虑“理发师悖论”，即在某个城镇中存在一个（男性）理发师，他为所有不给自己刮脸的男人刮脸，而仅仅为这些男人刮脸。证明这是一个矛盾的陈述：

Assume that such a barber exists in the town. Let's denote this barber as B. 
假设这个城镇中存在这样一位理发师。我们用 B 表示这个理发师。

Now, we consider the question of whether B shaves himself or not. There are two possibilities:
现在，我们考虑 B 是否给自己刮脸。有两种可能性：

1. If B shaves himself, then according to the statement of the paradox, B should not shave himself since he only shaves the men who do not shave themselves. This leads to a contradiction because B cannot simultaneously shave himself and not shave himself.
   如果 B 给自己刮脸，根据悖论陈述，B 不应该给自己刮脸，因为他只为不给自己刮脸的男人刮脸。这会导致一个矛盾，因为 B 不能同时给自己刮脸和不给自己刮脸。

2. If B does not shave himself, then according to the statement of the paradox, B should shave himself since he shaves all the men who do not shave themselves. Again, this leads to a contradiction because B cannot simultaneously shave himself and not shave himself.
   如果 B 不给自己刮脸，根据悖论陈述，B 应该给自己刮脸，因为他为所有不给自己刮脸的男人刮脸。同样，这会导致一个矛盾，因为 B 不能同时给自己刮脸和不给自己刮脸。

In both cases, we arrive at a contradiction. Therefore, it is impossible for such a barber to exist in the town. This paradox demonstrates the self-referential nature of the barber's statement and the logical inconsistency it leads to.
无论哪种情况，我们都得到了一个矛盾。因此，在这个城镇中不可能存在这样一位理发师。这个悖论展示了理发师陈述的自我参照性质以及由此引发的逻辑不一致性。

```lean
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
```

4. 记住，如果没有任何参数，类型为 ``Prop`` 的表达式只是一个断言。请填写下面的 ``prime`` 和 ``Fermat_prime`` 的定义，并构建每个给定的断言。例如，您可以通过断言对于每个自然数 ``n``，存在一个大于 ``n`` 的质数来表明存在无穷多个质数。哥德巴赫猜想认为，每个大于5的奇数都可以被三个质数相加。如果需要的话，请查找 Fermat 质数的定义或其它陈述的定义。

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

**翻译**

5. 尽可能证明存在量词部分列出的所有恒等式。

--------------------------------------------------------------

在这里，我们将尝试证明 Existential Quantifier 部分列出的一些恒等式。

1. ``∃x P(x) ∨ ∃x Q(x) ⇔ ∃x (P(x) ∨ Q(x))``*

假设存在某个元素 x，它满足性质 P(x) 或者存在某个元素 x，它满足性质 Q(x)。我们想要证明：存在某个元素 x，它同时满足 P(x) 或 Q(x)。

根据 Logic 中的合取分配律，我们可以将此恒等式拆分为两个分支进行证明。

**分支1**：假设存在某个元素 x，它满足性质 P(x)。那么存在某个元素 x，它同时满足 P(x) 或 Q(x)。

**分支2**：假设存在某个元素 x，它满足性质 Q(x)。那么存在某个元素 x，它同时满足 P(x) 或 Q(x)。

根据合取分配律，我们可以得出：存在某个元素 x，它同时满足 P(x) 或 Q(x)。因此，恒等式成立。

2. ``∃x P(x) ∧ ∃x Q(x) ⇔ ∃x (P(x) ∧ Q(x))``*

假设存在某个元素 x，它满足性质 P(x) 和存在某个元素 x，它满足性质 Q(x)。我们想要证明：存在某个元素 x，它同时满足 P(x) 和 Q(x)。

根据 Logic 中的析取分配律，我们可以将此恒等式拆分为两个分支进行证明。

**分支1**：假设存在某个元素 x，它满足性质 P(x)。那么存在某个元素 x，它同时满足 P(x) 和 Q(x)。

**分支2**：假设存在某个元素 x，它满足性质 Q(x)。那么存在某个元素 x，它同时满足 P(x) 和 Q(x)。

根据析取分配律，我们可以得出：存在某个元素 x，它同时满足 P(x) 和 Q(x)。因此，恒等式成立。

3. ``¬(∃x P(x)) ⇔ ∀x ¬P(x)``*

假设不存在任何元素 x，它满足性质 P(x)。我们想要证明：对于所有的元素 x，它都不满足性质 P(x)。

根据 Logic 中否定的存在量词规则，我们可以得出：对于所有的元素 x，它都不满足性质 P(x)。因此，恒等式成立。

4. ``∀x (P(x)∨ Q(x)) ⇔ (∀x P(x)) ∨ (∀x Q(x))``*

对于所有的元素 x，它满足性质 P(x) 或 Q(x)。我们想要证明：对于所有的元素 x，它满足性质 P(x) 或对于所有的元素 x，它满足性质 Q(x)。

根据 Logic 中析取的全称量词规则，我们可以将此恒等式拆分为两个分支进行证明。

**分支1**：对于所有的元素 x，它满足性质 P(x)。那么对于所有的元素 x，它满足性质 P(x) 或对于所有的元素 x，它满足性质 Q(x)。

**分支2**：对于所有的元素 x，它满足性质 Q(x)。那么对于所有的元素 x，它满足性质 P(x) 或对于所有的元素 x，它满足性质 Q(x)。

根据析取的全称量词规则，我们可以得出：对于所有的元素 x，它满足性质 P(x) 或对于所有的元素 x，它满足性质 Q(x)。因此，恒等式成立。

这是我们能够证明的一些存在量词部分列出的恒等式。其他的恒等式可能需要使用不同的推理法则或证明方式来完成。