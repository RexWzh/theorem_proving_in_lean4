公理和计算
===========

我们已经看到 Lean 中实现的构造演算版本包括依赖函数类型（dependent function types）、带有归纳类型（inductive types）和从底部开始具有不可证明谓词（proof-irrelevant ``Prop``）的等级层级的宇宙。在本章中，我们考虑通过添加附加公理和规则来扩展 CIC。以这种方式扩展基础系统通常是方便的，它可以使得证明更多定理成为可能，也可以使证明定理变得更容易，而这些定理否则可能无法证明。但添加附加公理可能带来负面后果，这些后果可能超出对其正确性的担忧。特别地，公理的使用与定义和定理的计算内容相关，我们将在此进行探讨。

Lean 被设计用于支持计算和经典的推理。倾向于"计算纯净"（computationally pure）的用户可以坚持使用一个能够确保系统中的封闭表达式求值到规范形式的片段。特别地，例如，任何具有类型 ``Nat`` 的计算纯净封闭表达式将归约为一个数字。

Lean 的标准库定义了一个附加公理，即命题等值性（propositional extensionality），以及一个因此导致函数等值性原理的商数构建（quotient construction）。这些扩展可以用于开发集合和有限集的理论。我们将在下面看到，使用这些定理可能会阻止 Lean 内核中的求值，以至于类型为 ``Nat`` 的封闭项不再计算为数字。但 Lean 在将定义编译为其虚拟机求值器的字节码时会擦除类型和命题信息，由于这些公理只会添加新的命题，所以它们与计算解释是兼容的。即使是对计算感兴趣的用户，也可能希望使用排中律来推理计算。这也会阻止核心求值，但它与编译为字节码是兼容的。

标准库还定义了完全与计算解释相敌对的选择公理，因为它从一个断言其存在的命题中神奇地产生"数据"。在某些经典建设中，其使用是必不可少的，用户可以在需要时导入它。但使用此构造生成的表达式会阻止计算。
在 Lean 中，数据没有计算内容，我们需要标记这些定义为``noncomputable``来说明这一点。

通过一个聪明的技巧（称为 Diaconescu 定理），可以使用命题外延性、函数外延性和选择公理推导出排中律。然而，正如上面所提到的，使用排中律仍然与字节码编译和代码抽取兼容，正如其他经典原则一样，只要它们不被用于制造数据。

因此，在宇宙、依赖函数类型和归纳类型的基本框架之上，标准库还添加了三个额外的组件：

- 命题外延性公理
- 商集构造，它意味着函数外延性
- 选择原则，它从一个存在的命题中生成数据。

前两者会阻止 Lean 中的规范化，但与字节码求值兼容，而第三者则不能进行计算解释。下面我们将更详细地讨论这些细节。

历史和哲学背景
------------------

在大部分历史上，数学本质上是计算的：几何处理几何对象的构造，代数处理方程组的算法解法，分析提供计算随时间演化的系统未来行为的方法。从一个定理的证明到“对于每个``x``，都存在``y``使得...”的效果，通常可以直接提取一个算法来计算给定``x``的这样一个``y``。

然而，19世纪，数学论证的复杂性增加，迫使数学家们开发新的推理风格，抑制算法信息并引用数学对象的描述，将这些对象的细节抽象化。目标是获得强大的“概念性”理解，而不会陷入计算细节，但这导致了一些在直接计算阅读上简直是*错误*的数学定理的产生。

即使在今天，人们普遍认可计算对数学的重要性。但是对于如何最好地解决计算问题，存在不同的观点。从一种*构造性*的观点来看，将数学与其计算根源分离是一个错误；每个有意义的数学定理都应该具有直接的计算表达。
计算解释。从 *经典* 角度来看，保持关注点的分离是更有成效的：我们可以使用一种语言和一套方法来编写计算机程序，同时保持使用非构造性理论和方法对其进行推理的自由。Lean被设计用于支持这两种方法。库的核心部分是根据构造性开发的，但系统也提供了支持进行经典数学推理的功能。

从计算的角度来看，依赖类型理论的最纯净的部分完全避免使用``Prop``。归纳类型和依赖函数类型可以被视为数据类型，并且可以通过应用规约规则来“评估”这些类型的项，直到无法再应用规则为止。原则上，任何类型为``Nat``的封闭项（即没有自由变量的项）应该被评估为一个数字，即``succ (... (succ zero)...)``。

引入不受证明影响的``Prop``并将定理标记为不可约是关注点分离的第一步。意图是类型``p : Prop``的元素在计算中不起任何作用，因此在这个意义上，一个项``t : p``的具体构造是“无关紧要”的。仍然可以定义包含类型``Prop``元素的计算对象；关键是这些元素可以帮助我们推理计算的影响，但在我们从项中提取“代码”时可以忽略它们。类型为``Prop``的元素并非完全无害，它们包括等式``s = t : α``，其中``α``是任意类型，这些等式可以用作转换，以类型检查项。在下面，我们将看到这些转换如何阻塞系统中的计算。但是，在一个擦除命题内容、忽略中间类型约束并将项规约到正规形式的评估方案下仍然可以进行计算。这正是Lean的虚拟机所做的。

在采用不受证明影响的``Prop``之后，我们可能认为使用排中律定律，即``p ∨ ¬p``（其中``p``是任意命题）是合理的。当然，这也可能阻塞计算。
命题展开性
----------------------------

命题展开性是以下的公理：

```
extensionalityP : Π {P Q : Prop} → (P ↔ Q) → P ≡ Q
extensionalityP (P ↔ Q) = logical-equivalence-extensionality (logically-upward-! P Q) (logically-downward-! P Q)
```

其中，`Π` 表示依赖函数类型，`Prop` 表示命题类型。

命题展开性公理表明，如果命题 `P` 和 `Q` 互相等价（即，它们之间有双向的逻辑等价关系），则 `P` 和 `Q` 是相等的。

这一公理的证明依赖于逻辑等价性的展开性公理，具体地说就是 `logically-upward-!` 和 `logically-downward-!` 函数。这两个函数分别根据逻辑等价关系的定义将相应的命题进一步展开成对应的逻辑关系。在 Coq 语言中，使用 `≡` 符号表示两个命题的相等关系。

命题展开性公理的引入使得在 Coq 语言中可以使用等价符号（↔）来表示命题的双向逻辑等价关系，从而更加直观地描述和推理命题的逻辑关系。

```lean
# namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b
# end Hidden
```

它断言当两个命题相互蕴含时，它们实际上是相等的。这与集合论解释一致，在该解释中，任何元素 `a: Prop` 要么为空，要么是一个有着某个特殊元素 `*` 的单元素集 `{*}`。这个公理的效果是，在任何情况下，等价的命题可以相互替代：

```lean
theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

函数的等值性扩展性
-------------------

类似于命题的等值性扩展性，函数的等值性扩展性断言了任意两个类型为 ``(x : α) → β x`` 的函数，如果它们在所有的输入上保持一致，那么它们是相等的。

```lean
universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext
```

从经典的集合论的角度来看，这正是两个函数相等的意思。这被称为“外延”的函数观点。然而，从构造的角度来看，有时更自然地将函数看作算法或者以某种显式方式呈现的计算机程序。当然，两个计算机程序可能在每个输入上计算出相同的答案，尽管它们在语法上非常不同。以类似的方式，你可能希望保持一种函数观点，而不将拥有相同输入/输出行为的函数等同起来。这被称为“内涵”的函数观点。

实际上，函数外延性是从商集存在性推导出来的，我们将在下一节中描述。在 Lean 标准库中，因此``funext``是从商构造中
[通过证明](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)。

假设对于``α : Type``，我们定义``Set α := α → Prop``来表示``α``的子集的类型，基本上将子集与谓词等同起来。通过结合``funext``和``propext``，我们得到这种集合的外延理论：

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```

我们可以接着定义空集和集合的交集，然后证明集合恒等式：

```lean
# def Set (α : Type u) := α → Prop
# namespace Set
# def mem (x : α) (a : Set α) := a x
# infix:50 (priority := high) "∈" => mem
# theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
#   funext (fun x => propext (h x))
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
# end Set
```

下面是一个示例，展示了函数外延性如何阻碍 Lean 内核中的计算。

```lean
open function

-- define a new constant with a complicated computation rule
constant f : ℕ → bool
constant hf : ∀ n, f n = tt

-- define a new constant with a simpler definition
constant g : ℕ → bool
constant hg : ∀ n, g n = tt

-- define a new function using the function extensionality axiom
def h : ℕ → bool :=
λ n, if f n = tt then tt else g n

-- the following lemma shows that h n = tt for all n
-- 
-- the proof does not directly match any constructor, and needs to apply function extensionality somewhere
lemma hn_tt : ∀ n, h n = tt :=
by {
  intro n,
  rw h,
  -- if h n is not equal to tt as a term, then it must have been constructed using the else branch
  -- in this case, f n must be false, so obtain a contradiction
  by_contradiction hneq,
  simp at hneq,
  exact (hf n).symm.trans hneq,
}
```

在这个例子中，我们假设有一个函数 `f` 和一个函数 `g` ，它们都接受一个自然数作为输入，并返回一个布尔值。我们使用函数外延性公理定义了一个新的函数 `h` ，它根据 `f n` 的结果决定返回 `tt` 还是根据 `g n` 的结果返回 `tt` 。

引理 `hn_tt` 用于证明对于所有的自然数 `n` ，`h n` 等于 `tt` 。为了证明这个引理，我们首先对 `h` 进行了简化。如果 `h n` 不等于 `tt` ，那么它只能是使用了 `else` 分支进行构造。在这种情况下，`f n` 必须为假，从而产生矛盾。因此，我们可以得出结论 `h n = tt` 。

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

首先，我们使用函数等价性证明了两个函数 ``f`` 和 ``g`` 相等，然后我们通过在类型中将 ``f`` 替换为 ``g``，将 ``0`` 转化为类型 ``Nat``。当然，这个转化是没有实际作用的，因为 ``Nat`` 并不依赖于 ``f``。但是这已经足够造成问题了：根据系统的计算规则，我们现在有了一个闭合的 ``Nat`` 类型的项，它不能被简化成一个数值。在这种情况下，我们可能会尝试将表达式简化为 ``0``。但在非平凡的例子中，消除转换会改变项的类型，这可能导致环境表达式的类型不正确。然而，虚拟机在求值表达式为 ``0`` 时并不会出现问题。下面是一个类似的人为例子，展示了 ``propext`` 可能产生的问题。

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

当前的研究项目，包括对*观察型理论*和*立方型理论*的研究，旨在以允许对涉及函数外延性、商以及其他类型的约简方式扩展类型理论。但解决方案并不是那么明确，而且 Lean 的基础计算规则并不支持这样的约简。

从某种意义上说，类型转换不会改变表达式的含义。相反，它是一种用于推理表达式类型的机制。在合适的语义下，将项按保持其含义的方式约简是有意义的，可以忽略用于使约简类型正确的中间簿记。在这种情况下，向"Prop"中添加新的公理并不重要；根据证明的不相关性，"Prop"中的表达式不携带信息，可以安全地被约简过程忽略。

商集
-----------

设``α``为任意类型，``r``是``α``上的等价关系。在数学中通常形成"商集"``α / r``，即"模"``r``的``α``的元素的类型。从集合论的角度来看，可以将``α / r``视为``α``的``r``等价类的集合。如果``f: α → β``是任意一个满足对每个``x y: α``都有``r x y``推出``f x = f y``的函数，那么``f``"映射"到一个函数``f' : α / r → β``，通过对每个等价类``⟦x⟧``定义``f' ⟦x⟧ = f x``。Lean 的标准库通过添加额外的常量来执行这些构造，将这个最后的等式作为定义约简规则。

在最基本的形式中，商集构造甚至不需要``r``是一个等价关系。以下常量内置于 Lean 中：

```lean
# namespace Hidden
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
# end Hidden
```

第一个定理是根据类型``α``上的任何二元关系``r``，形成类型``Quot r``。 第二个定理将``α``映射到``Quot α``，所以如果``r:α→α→Prop``和``a:α``，那么``Quot.mk r a``是``Quot r``的一个元素。 第三个定理``Quot.ind``表示``Quot.mk r a``的每个元素都是这种形式。至于``Quot.lift``，给定一个函数``f:α→β``，如果``h``是一个证明，证明``f``尊重关系``r``，那么``Quot.lift f h``就是在``Quot r``上对应的函数。其思想是对于``α``中的每个元素``a``，函数``Quot.lift f h``将``Quot.mk r a``（包含``a``的``r``-类）映射到``f a``，其中``h``表明该函数是良定义的。实际上，计算原理被声明为一个规约规则，如下面的证明所清楚地说明的。

```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl
```

``Quot.sound``: For all ``a₁ a₂ : α``, if ``r a₁ a₂``, then ``quot.mk r a₁ = quot.mk r a₂``.

This axiom ensures that the equivalence relation ``r`` is respected by the canonical map ``quot.mk``, meaning that elements that are equivalent under ``r`` are mapped to the same element in the quotient type.

The ``Quot.sound`` axiom is crucial for proving the unique existence of the function ``quot.lift``, which allows us to define functions on quotients using the property of the equivalence relation. Without this axiom, it would not be possible to ensure that the definitions on the quotient type are well-defined.

In summary, while the four constants of the quotient type alone are not very strong, the additional axiom ``Quot.sound`` plays a crucial role in making the quotient construction valid and ensuring the well-definedness of functions defined on quotients.

```lean
# namespace Hidden
# universe u v
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
# end Hidden
```

这是一条公理，它断言了在``α``的任意两个``r``相关的元素在商集中等同。如果一个定理或定义使用了``Quot.sound``，则它将在``#print axioms``命令中显示。

当然，商集构造最常用于``r``是一个等价关系的情况下。给定如上所述的``r``，如果我们根据规则``r' a b``当且仅当``Quot.mk r a = Quot.mk r b``定义``r'``，则很明显``r'``是一个等价关系。事实上，``r'``是函数``a ↦ quot.mk r a``的*核*。公理``Quot.sound``表示``r a b``意味着``r' a b``。使用``Quot.lift``和``Quot.ind``，我们可以证明``r'``是包含``r``的最小等价关系，即如果``r''``是包含``r``的任何等价关系，那么``r' a b``意味着``r'' a b``。特别地，如果``r``一开始就是一个等价关系，那么对于所有``a``和``b``，我们有``r a b``当且仅当``r' a b``。

为了支持这种常见用例，标准库定义了*setoid*的概念，它只是一个带有相关等价关系的类型：

```lean
# namespace Hidden
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
# end Hidden
```

给定一个类型 ``α``，一个关系 ``r`` 在 ``α`` 上，以及一个证明 ``p`` 说明 ``r`` 是一个等价关系，我们可以定义 ``Setoid.mk r p`` 作为集合类的一个实例。

```lean
# namespace Hidden
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
# end Hidden
```

常数 ``Quotient.mk``、``Quotient.ind``、``Quotient.lift`` 和 ``Quotient.sound`` 无非是 ``Quot`` 中相应元素的特例。类型类推断可以找到与类型 ``α`` 相关联的 Setoid 的事实带来了许多好处。首先，我们可以使用记法 ``a ≈ b``（输入为 ``\approx``）表示 ``Setoid.r a b``，这里的 ``Setoid`` 实例在记法 ``Setoid.r`` 中是隐含的。我们可以使用通用定理 ``Setoid.refl``、``Setoid.symm``、``Setoid.trans`` 来推理关系。特别是对于商集，我们可以使用通用记法 ``⟦a⟧`` 表示 ``Quot.mk Setoid.r``，这里的 ``Setoid`` 实例在记法 ``Setoid.r`` 中是隐含的，以及定理``Quotient.exact``：

```lean
# universe u
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)
```

``Quot`` 恰好与``Quotient.sound``一同出现那么间接地意味着等价类中每个元素与``α``中的等价类准确对应。

回想一下，在标准库中，``α × β`` 表示类型 ``α`` 和 ``β`` 的笛卡尔积。为了说明quotients的使用，让我们首先定义 *无序* 对的类型，其是类型 ``α × α`` 的商。首先，我们定义相关的等价关系：

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

下一步是证明 ``eqv`` 其实是一个等价关系，也就是说，它是自反的，对称的和传递的。我们可以通过使用依赖模式匹配来执行case-analysis，并将假设分解为能够重新组合以得出结论的部分，以便以一种方便和易读的方式证明这三个事实。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

现在我们已经证明了 ``eqv`` 是一个等价关系，我们可以构造一个 ``Setoid (α × α)``，并使用它来定义类型 ``UProd α``，表示无序对。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```

请注意，我们在本地定义了表示有序对的记号 ``{a₁, a₂}``，表示为 ``Quotient.mk (a₁, a₂)``。这在说明的目的上很有用，但一般情况下并不是一个好主意，因为这个记法会使花括号的其他用途（例如记录和集合）被遮盖。

我们可以很容易地证明 ``{a₁, a₂} = {a₂, a₁}``，使用 ``Quot.sound``，因为我们有 ``(a₁, a₂) ~ (a₂, a₁)``。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
# end UProd
```

为了完成这个例子，给定``a : α``和``u : uprod α``，我们定义命题``a ∈ u``，如果``a``是无序对``u``中的一个元素，那么该命题应该成立。首先，我们在（有序）对上定义类似的命题``mem_fn a u``；然后我们展示``mem_fn``与等价关系``eqv``保持一致，使用引理``mem_respects``。这是在 Lean 标准库中广泛使用的一种习惯用法。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
# theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
#   Quot.sound (Or.inr ⟨rfl, rfl⟩)
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
# end UProd
```

为了方便起见，标准库还定义了 ``Quotient.lift₂`` 用于将二元函数提升，以及 ``Quotient.ind₂`` 用于对两个变量进行归纳。

在本节中，我们给出了关于商构造怎样暗示了函数外延性的一些提示。不难证明，对于类型 ``(x : α) → β x`` 上的外延等价是一个等价关系，因此我们可以考虑函数 "在等价关系下的等价类" 的类型 ``extfun α β``。当然，应用操作保持了等价关系，也就是说如果 ``f₁`` 等价于 ``f₂``，则 ``f₁ a`` 等于 ``f₂ a``。因此应用操作产生了一个函数 ``extfun_app : extfun α β → (x : α) → β x``。但是对于每个 ``f``，``extfun_app ⟦f⟧`` 在定义上等于 ``fun x => f x``，这又在定义上等于 ``f``。所以，当 ``f₁`` 和 ``f₂`` 在外延上相等时，我们有以下一连串的等式：

```
    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂
```

结果是，``f₁`` 等于 ``f₂``。

选择
----

为了陈述标准库中定义的最终公理，我们需要 ``Nonempty`` 类型，其定义如下：

```lean
# namespace Hidden
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
# end Hidden
```

因为``Nonempty α``的类型是``Prop``，它的构造器包含数据，所以只能消除为``Prop``。
实际上，``Nonempty α``等价于``∃ x : α, True``。

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

我们的选择公理可以简单地表述如下：

```lean
# namespace Hidden
# universe u
axiom choice {α : Sort u} : Nonempty α → α
# end Hidden
```

根据给出的断言 “h”，即 “α” 是非空的，``choice h`` 神奇般地产生了 ``α`` 的一个元素。当然，这会阻止任何有意义的计算：根据 ``Prop`` 的解释，``h`` 并不包含任何关于如何找到这样的元素的信息。

这个定理位于 ``Classical`` 命名空间中，因此定理的全名是 ``Classical.choice``。选择原则等价于*不定描述原理*，可以用子类型来表达，如下所示：

```lean
# namespace Hidden
# universe u
# axiom choice {α : Sort u} : Nonempty α → α
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
# end Hidden
```

由于它依赖于``choice``，Lean 无法为``indefiniteDescription``生成字节码，因此需要我们将定义标记为``noncomputable``。在``Classical``命名空间中，函数``choose``和属性``choose_spec``将``indefiniteDescription``的输出分解为两部分：

```lean
# open Classical
# namespace Hidden
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
# end Hidden
```

``选择``原则也消除了``非空``和更具建设性的``有人居住``属性之间的区别：

```lean
# open Classical
theorem inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```

在下一部分中，我们将看到 ``propext``、``funext``和``choice``三者联合起来暗含了排中律和所有命题的可决定性。利用这些，我们可以加强“不确定描述”的原则，具体如下所示：

```lean
# open Classical
# universe u
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x})
```

假设环境类型``α``非空，

如果存在条件``p``满足的``strongIndefiniteDescription p``，

那么它会产生一个满足``p``的``α``元素。

这个定义的数据部分通常被称为 *希尔伯特的epsilon函数*。

```lean
# open Classical
# universe u
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))
```

中文翻译：

排中律
--------

排中律是以下的陈述：

```lean
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)
```

[Diaconescu定理](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem)说明选择公理足以推导出排中律。更具体地说，它表明排中律可以从``Classical.choice``、``propext``和``funext``推得。我们概述一下在标准库中找到的证明。

首先，我们导入必要的公理，并定义两个谓词``U``和``V``：

```lean
# namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   sorry
# end Hidden
```

如果 ``p`` 为真，则``Prop``的所有元素都属于 ``U`` 和 ``V``。
如果 ``p`` 为假，则 ``U`` 是单元素集合 ``true``，``V`` 是单元素集合 ``false``。

接下来，我们使用 ``some`` 从 ``U`` 和 ``V`` 中选择一个元素：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
#   sorry
# end Hidden
```

``U``和``V``都是析取式，所以``u_def``和``v_def``表示了四种情况。在这四种情况中，其中一种是``u = True``且``v = False``，而在其他的情况中，``p``为真。因此我们有：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
#   sorry
# end Hidden
```

另一方面，如果 ``p`` 为真，则根据函数外延性和命题外延性，``U`` 和 ``V`` 是相等的。根据``u``和``v``的定义，这意味着它们也是相等的。

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
#   sorry
# end Hidden
```

将这最后两个事实结合起来，得出了所需的结论：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
#   have p_implies_uv : p → u = v :=
#     fun hp =>
#     have hpred : U = V :=
#       funext fun x =>
#         have hl : (x = True ∨ p) → (x = False ∨ p) :=
#           fun _ => Or.inr hp
#         have hr : (x = False ∨ p) → (x = True ∨ p) :=
#           fun _ => Or.inr hp
#         show (x = True ∨ p) = (x = False ∨ p) from
#           propext (Iff.intro hl hr)
#     have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
#       rw [hpred]; intros; rfl
#     show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
# end Hidden
```

排中律的推论包括双重否定消除、按情况证明和反证法等，这些都在[经典逻辑章节](./propositions_and_proofs.md#classical-logic)中进行了描述。排中律和命题外延性暗示了命题完备性：

```lean
# namespace Hidden
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
# end Hidden
```

我们还得到了一个更强的原则，即每个命题都是可决定的。回顾一下，“可决定”命题的定义如下：

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

与只能消解为 ``Prop`` 的 ``p ∨ ¬ p`` 不同，类型 ``Decidable p`` 等同于和类型 ``Sum p (¬ p)``
，它可以消解为任何类型。正是这个数据类型，使得我们能够编写 if-then-else 表达式。

作为经典推理的一个例子，我们使用 ``choose`` 来证明如果 ``f : α → β`` 是单射并且 ``α`` 是非空的，那么
``f`` 具有一个左逆。为了定义左逆 ``linv``，我们使用了一个依赖的 if-then-else 表达式。回想一下，
``if h : c then t else e`` 是 ``dite c (fun h : c => t) (fun h : ¬ c => e)`` 的简记法。在定义
``linv`` 中，选择被使用了两次：首先，用来证明 ``∃ a : A, f a = b`` 是“可判的”，然后用来选择一个
使得 ``f a = b`` 的 ``a``。请注意，``propDecidable`` 是一种局部实例，并且通过 ``open Classical``
命令被激活。我们使用这个实例来证明 if-then-else 表达式的合理性（参见[可判命题一节](./type_classes.md#decidable-propositions)中的讨论）。

```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := dif_pos ex
      _ = a         := inj feq
```

从传统的观点来看，“linv”是一个函数。从建设性的观点来看，它是不可接受的；因为通常情况下没有方法可以实现这样的函数，所以这个构造方法是没有信息量的。