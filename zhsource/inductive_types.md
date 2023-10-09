归纳类型
=============

我们已经看到，Lean 的形式基础包括基本类型 ``Prop, Type 0, Type 1, Type 2, ...``，并且允许形成依赖函数类型 ``(x : α) → β``。在示例中，我们还使用了其他类型，如 ``Bool``, ``Nat``, ``Int``，以及类型构造函数，如 ``List`` 和乘积 ``×``。实际上，在 Lean 的库中，除了宇宙和依赖箭头之外的每个具体类型，以及除了依赖箭头之外的每个类型构造函数，都是归纳类型的一个实例。令人惊讶的是，可以仅基于类型宇宙、依赖箭头类型和归纳类型来构建数学的实质性结构；其他所有内容都是从这些基础上推导出来的。

直观地说，归纳类型是从指定的构造函数列表构建起来的。在 Lean 中，指定此类类型的语法如下：

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

直观地说，每个构造函数都指定了一种从``Foo``的先前构造值中构建新对象的方式。类型``Foo``仅由以这种方式构建的对象组成。归纳声明中的第一个字符``|``是可选的。我们还可以使用逗号而不是``|``来分隔构造函数。

我们将在下面看到，构造函数的参数可以包括类型为``Foo``的对象，但需要满足一定的“正性”约束，这保证了``Foo``的元素从底部向上构建。粗略地说，每个``...``可以是从``Foo``和先前定义的类型构造的任何箭头类型，其中``Foo``（如果存在）仅出现为依赖箭头类型的“目标”。

我们将提供一些归纳类型的示例。我们还将考虑上面方案的轻微推广，即相互定义的归纳类型和所谓的*归纳族*。

与逻辑联结词一样，每个归纳类型都具有引入规则，显示如何构造该类型的元素，并具有消除规则，显示如何在另一构造中“使用”该类型的元素。与逻辑联结词的类比应该不会令人惊讶；正如我们将在下面看到的，它们也是归纳类型构造的例子。您已经见过归纳类型的引入规则：它们只是在类型定义中指定的构造函数。消除规则提供了对该类型的递归原则，其中包括归纳原则作为一种特殊情况。

在下一章中，我们将介绍Lean的函数定义包，它提供了更方便的方式来定义在归纳类型上的函数并进行归纳证明。但是由于归纳类型的概念非常基础，我们认为从一个低级的、亲身实践的理解开始是很重要的。我们将先从一些基本的归纳类型示例开始，然后逐步提升到更复杂和复杂的示例。

枚举类型
------------

最简单的归纳类型是具有有限、枚举列表的类型。

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

``inductive`` 命令创建了一个新的类型 ``Weekday``。所有的构造函数都存在于 ``Weekday`` 命名空间中。

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#check Weekday.sunday
#check Weekday.monday

open Weekday

#check sunday
#check monday
```

当声明`Weekday`归纳类型时，可以省略`：Weekday`。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

将``sunday``，``monday``，...，``saturday``视为``Weekday``的互不相同的元素，并且没有其他区别性质。消除原则``Weekday.rec``与类型``Weekday``及其构造函数一起定义。它也被称为一个*递归器*，它使得类型“归纳”:它允许我们通过为每个构造器分配值来在``Weekday``上定义一个函数。直观上讲，归纳类型完全由构造器生成，并且没有超出其构造器构造的元素。

我们将使用`match`表达式来定义一个从``Weekday``到自然数的函数：

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3
```

注意，`match` 表达式是使用在声明归纳类型时生成的 *递归体* `Weekday.rec` 进行编译的。

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/
```

在声明归纳数据类型时，可以使用 `deriving Repr` 来指导 Lean 自动生成一个将 `Weekday` 对象转换为文本的函数。这个函数被 `#eval` 命令用于显示 `Weekday` 对象。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```

通常情况下，将与一个结构相关的定义和定理分组放在具有相同名称的命名空间中非常有用。例如，我们可以将`numberOfDay`函数放在`Weekday`命名空间中。然后，在打开命名空间时，我们可以使用更短的名称。

我们可以定义从`Weekday`到`Weekday`的函数：

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```

我们如何证明通用定理 “``next (previous d) = d``” 对于任意星期 “``d``” 都成立？我们可以使用 `match` 来为每个构造器提供一个证明。

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```

使用策略证明，我们可以更加简洁地表达：

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

下面的《归纳类型的策略》将介绍一些专门用于归纳类型的策略。

注意，在命题即类型的对应关系下，我们不仅可以使用 ``match`` 来证明定理，还可以定义函数。换句话说，在命题即类型的对应关系下，按情况进行证明就是按情况进行定义，只是所“定义”的是一个证明而不是一段数据。

Lean 库中的 `Bool` 类型是一个枚举类型的实例。

```lean
# namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool
# end Hidden
```

（为了运行这些示例，我们将它们放在一个名为“Hidden”的命名空间中，这样像“Bool”这样的名称就不会与标准库中的“Bool”冲突。这是必要的，因为这些类型是Lean“预导入的”类型，当系统启动时会自动导入。）

作为一个练习，你应该考虑一下这些类型的引入和消除规则是做什么的。作为进一步的练习，我们建议在“Bool”类型上定义布尔运算“and”、“or”、“not”，并验证常见的恒等式。请注意，你可以使用`match`来定义像`and`这样的二元运算：

```lean
# namespace Hidden
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
# end Hidden
```

同样地，大多数身份可以通过引入适当的“match”，然后使用``rfl``来证明。

带有参数的构造函数
----------------

枚举类型是归纳类型的特殊情况，其中构造函数根本不带任何参数。一般来说，“构造”可以依赖于数据，然后以构造的参数表示。考虑库中对乘积类型和和类型的定义：

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
# end Hidden
```

在这些例子中请考虑以下情况。
乘积类型（product type）有一个构造函数，``Prod.mk``，它接受两个参数。为了在``Prod α β``上定义一个函数，我们可以假设输入是``Prod.mk a b``的形式，我们需要指定输出是关于``a``和``b``的。我们可以用这个来定义``Prod``的两个投影（projection）。请记住，标准库为``Prod α β``定义了记法``α × β``，并为``Prod.mk a b``定义了记法``(a, b)``。

```lean
# namespace Hidden
# inductive Prod (α : Type u) (β : Type v)
#   | mk : α → β → Prod α β
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
# end Hidden
```

函数 ``fst`` 接收一个二元组 ``p``。`match` 将 ``p`` 解释为一个二元组 ``Prod.mk a b``。此外，回顾一下[依赖类型理论](./dependent_type_theory.md)中的内容，为了使这些定义尽可能地具有普遍性，我们允许类型 ``α`` 和 ``β`` 属于任何宇宙。

下面是另一个示例，我们使用了替代 `match` 的递归器 `Prod.casesOn`。

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)
```

参数 `motive` 用于指定您想要构建的对象的类型，它是一个函数，因为它可能依赖于这对值。函数 ``cond`` 是一个布尔条件函数：如果 ``b`` 为真，则返回 ``t1``，否则返回 ``t2``。函数 ``prod_example`` 接受一个由一个布尔值 ``b`` 和一个数字 ``n`` 组成的对，并根据 ``b`` 的真假返回 ``2 * n`` 或 ``2 * n + 1``。

相比之下，和类型有 *两个* 构造方法，分别是 ``inl`` 和 ``inr``（表示 "插入左侧" 和 "插入右侧"），每个方法都接受 *一个* （显式的）参数。为了在 ``Sum α β`` 上定义一个函数，我们必须处理两种情况：要么输入的形式是 ``inl a``，在这种情况下我们必须用 ``a`` 指定一个输出值；要么输入的形式是 ``inr b``，在这种情况下我们必须用 ``b`` 指定一个输出值。

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)
```

这个示例与前面的示例类似，但现在 ``sum_example`` 的输入隐式地可以是 ``inl n`` 或 ``inr n`` 这种形式。第一种情况下，该函数返回 ``2 * n``，第二种情况下，返回 ``2 * n + 1``。

注意，产品类型依赖于参数 ``α β : Type``，它们是构造函数和 ``Prod`` 的参数，Lean 会检测到这些参数是否可以从后面的构造函数的参数或返回类型推断出来，并在那种情况下将它们设置为隐式参数。

在 [定义自然数](#定义自然数) 部分，我们将看到当归纳类型的构造函数从该归纳类型本身接收参数时会发生什么。这一节考虑的示例的特点是每个构造函数只依赖于先前指定的类型。

注意，具有多个构造函数的类型是离散的：``Sum α β`` 的元素可以是 ``inl a`` 这种形式，也可以是 ``inr b`` 这种形式。具有多个参数的构造函数引入了合取信息：从 ``Prod α β`` 的元素 ``Prod.mk a b`` 中我们可以提取出 ``a``和 ``b``。任意的归纳类型可以包含这两个特性，具有任意数量的构造函数，每个构造函数可以接收任意数量的参数。

与函数定义类似，Lean 的归纳定义语法可以让你在冒号之前给构造函数指定参数的名称：

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
# end Hidden
```

这些定义的结果与本节早先给出的结果本质上是一样的。

像``Prod``这样只有一个构造器的类型，是纯连词型的：构造器只是将参数列表打包成一个数据单元，本质上是一个元组，后续参数的类型可以依赖于初始参数的类型。我们也可以将这样的类型视为“记录”或者“结构”。在 Lean 中，关键字``structure``可以用来定义这样一个归纳类型以及它的投影，同时进行。

```lean
# namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
# end Hidden
```

这个例子同时介绍了归纳类型``Prod``，它的构造函数``mk``，通常的消除器（``rec``和``recOn``），以及如上定义的投影函数``fst``和``snd``。

如果你不给构造函数命名，Lean会默认使用``mk``。例如，以下定义了一个用于存储颜色的三个RGB值的记录：

```lean
structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

"yellow" 的定义形成了具有三个值的记录，并且投影 "Color.red" 返回红色分量。

如果在每个字段之间添加换行符，您可以避免使用括号。

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr
```

``structure`` 命令在定义代数结构方面特别有用，Lean 提供了大量支持这方面工作的基础设施。下面是一个半群的定义示例：
```lean
structure semigroup (α : Type*) extends has_mul α :=
(mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c))
```
在这个定义中，我们使用了 ``structure`` 关键字来定义一个类型为 $\alpha$ 的半群。``extends`` 关键字意味着我们要将 ``has_mul`` 这个类型的实例作为参数传递给半群，并在定义中使用它。实际上，这意味着我们在定义中同时定义了半群的乘法运算。``mul_assoc`` 是半群的结合律。

正如上面的注释所提到的，关键字 ``structure`` 允许我们定义和组织复杂的代数结构。结构体中的字段可以是函数、定理甚至其他结构体，允许我们以更高层次的抽象和精确度来描述数学对象。

使用 ``structure`` 命令定义代数结构后，我们可以使用 Lean 提供的丰富的工具和定理来操作和做推理。这些工具包括自动生成实例、定义新概念和构造证明等。例如，我们可以通过 ``apply`` 策略来使用定义中的等式证明结合律，或者通过使用 ``rw`` 策略来将定义中的等式应用到目标上，以便对目标进行替换。

总而言之，Lean 提供了一个强大的基础设施来处理代数结构的定义和操作，使我们能够进行更加严密和清晰的数学证明。

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

我们将在[第9节 结构和记录](./structures_and_records.md)中看到更多的例子。

我们已经讨论了依赖积类型 `Sigma`：

```lean
# namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
# end Hidden
```

在库中还有两个归纳类型的例子如下：

First, we have the type of vectors, which generalises lists to arbitrary lengths. A vector of `A`s of length `n` is given by the following constructors:
- `nil : vector A 0` constructs the empty vector,
- `cons : A → vector A n → vector A (n + 1)` adds an element to the front of a vector.

This type is defined in Lean's standard library as:

```lean
inductive vector (A : Type u) : ℕ → Type u
| nil : vector 0
| cons {n : ℕ} : A → vector n → vector (n + 1)
```

For example, the type `vector ℕ 3` represents all vectors of natural numbers of length 3, such as `[1, 2, 3]`.

Second, we have the type of trees, which generalises binary trees to arbitrary branching factors. A tree of `A`s is given by the following constructors:
- `leaf : A → tree A` constructs a leaf node with a value of type `A`,
- `node : list (tree A) → tree A` constructs a non-leaf node with a list of subtrees.

This type is also defined in Lean's standard library as:

```lean
inductive tree (A : Type u)
| leaf : A → tree
| node : list tree → tree
```

For example, the type `tree ℕ` represents all trees of natural numbers, such as a tree with a single leaf `[leaf 1]` or a tree with two levels `[node [leaf 1, leaf 2], leaf 3]`.

These examples showcase the power and flexibility of inductive types in Lean, which allow us to define and reason about a wide range of data structures in a type-safe and elegant manner.

```lean
# namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
# end Hidden
```

在依赖类型理论的语义中，没有内建的部分函数概念。函数类型 ``α → β`` 或依赖函数类型 ``(a : α) → β`` 的每个元素都被假设在每个输入上都有一个值。``Option`` 类型提供了一种表示部分函数的方式。``Option β`` 类型的元素可以是 ``none`` 或形如 ``some b`` 的形式，其中``b: β``。因此，我们可以将类型为 ``α → Option β`` 的元素 ``f`` 视为从 ``α`` 到 ``β`` 的部分函数：对于每个 ``a : α``，``f a`` 要么返回 ``none``，表示 ``f a`` 为“未定义”，要么返回 ``some b``。

``Inhabited α`` 的元素简单地证明了 ``α`` 存在一个元素。稍后，我们将看到 ``Inhabited`` 是 Lean 中的一个*类*示例：可以教会 Lean 适当的基本类型是有一个元素，并且可以基于此自动推断其他构造类型是有一个元素的。

作为练习，我们鼓励你为从 ``α`` 到 ``β`` 和从 ``β`` 到 ``γ`` 的部分函数发展一个组合的概念，并展示它的行为符合预期。我们还鼓励你证明 ``Bool`` 和 ``Nat`` 是有元素的，两个有元素类型的乘积也是有元素的，以及函数类型到一个有元素类型的类型也是有元素的。

归纳定义的命题
------------

归纳定义的类型可以存在于任何类型宇宙中，包括最底层的 ``Prop``。事实上，这正是逻辑连接词是如何定义的。

```lean
# namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
# end Hidden
```

你应该考虑这些是如何产生你已经见过的引入和消除规则的。有一些规则可以指导归纳类型的消解*去*，也就是说，可以作为递归器目标的类型的种类。粗略地说，在``Prop``中特征化归纳类型的东西是只能消解为``Prop``中的其他类型。这与对``p: Prop``情况一致，元素``hp: p``不携带任何数据。然而，此规则有一个小例外，我们将在下面[归纳家族](#inductive-families)部分讨论。

即使存在量词也是归纳定义的：

```lean
# namespace Hidden
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
# end Hidden
```

请注意，符号“``∃ x : α, p``”是“``Exists (fun x : α => p)``”的语法糖。

“``False``”、“``True``”、“``And``”和“``Or``”的定义与“``Empty``”、“``Unit``”、“``Prod``”和“``Sum``”的定义完全相似。不同之处在于前者产生“``Prop``”类型的元素，而后者产生具有某个“``u``”类型的“``Type``”类型的元素。类似地，“``∃ x : α, p``”是“``Σ x : α, p``”的“``Prop``”值变体。

这是提及另一种归纳类型的好地方，称为“``{x : α // p}``”，它有点像“``∃ x : α, P``”和“``Σ x : α, P``”之间的混合体。

```lean
# namespace Hidden
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
# end Hidden
```

事实上，在 Lean 中，``Subtype`` 是使用 ``structure`` 命令定义的：

```lean
# namespace Hidden
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
# end Hidden
```

"``{x : α // p x}``" 的表示是 "``Subtype (fun x : α => p x)``" 的语法糖。
它借鉴了集合论中的子集符号表示法：其想法是 "``{x : α // p x}``"
表示的是具有性质 "``p``" 的元素的集合。

定义自然数
---------------

到目前为止，我们所看到的归纳定义类型都是“平的”：
构造函数将数据包装并插入到类型中，相应的递归函数则将数据拆分出来并对其进行操作。当构造函数作用于正在定义的类型的元素上时，情况变得更加有趣。一个典型的例子是自然数类型 "``Nat``"：

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
# end Hidden
```

有两个构造函数。我们从 ``zero : Nat`` 开始；它不接受任何参数，所以我们一开始就有它。相比之下，构造函数 ``succ`` 只能应用于先前构造的 ``Nat``。将它应用于 ``zero`` 得到 ``succ zero : Nat``。再次应用它得到 ``succ (succ zero) : Nat``，依此类推。直观地说，``Nat`` 是具有这些构造函数的“最小”类型，意味着通过从 ``zero`` 开始，反复应用 ``succ`` 可以彻底（和自由地）生成它。

与之前一样，``Nat`` 的递归器旨在定义一个从 ``Nat`` 到任何域的依赖函数 ``f``，即 ``motive : Nat → Sort u`` 的元素 ``(n : Nat) → motive n``。它必须处理两种情况：输入为 ``zero`` 的情况，和输入为形如 ``succ n`` 的情况（其中 ``n : Nat``）。在第一种情况下，我们只需指定与适当类型匹配的目标值，与之前一样。然而，在第二种情况下，递归器可以假设已经计算出了 ``n`` 处的 ``f`` 的值。因此，递归器的下一个参数指定了如何根据 ``n`` 和 ``f n`` 的值来计算 ``f (succ n)`` 的值。如果我们检查递归器的类型，

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#check @Nat.rec
# end Hidden
```

**The Lean Theorem Prover**

*This document describes the Lean theorem prover language and system. It is intended as a reference manual and also contains a brief description of how to install and use Lean.*

Lean is an open-source theorem prover developed at Microsoft Research. It is based on dependently typed functional programming and proof assistants, combining aspects of both. Lean allows users to write formal proofs using a powerful type system and constructs logic statements that can be checked for validity by the Lean kernel.

Lean's syntax is similar to that of many modern programming languages, making it easy for programmers to learn. The language supports advanced features such as dependent types, inductive families, type classes, and higher-order logic. Lean's type system is fully integrated with its programming features, allowing users to write functions and prove theorems in the same language.

Lean provides a rich set of tools for exploring and manipulating formal proofs. Users can interact with proofs using tactics, which are commands that guide the proof search process. Lean also includes a powerful automation tool called `simp` that can simplify complicated expressions and proofs automatically.

The Lean theorem prover has been used to formalize significant parts of mathematics and computer science. It has been applied to fields such as category theory, algebra, analysis, and computer verification. Lean is designed to be extensible and modular, allowing users to define their own theories and proof tactics.

Lean is supported by an active and friendly community of users and developers. The community provides a wealth of resources, including tutorials, examples, and documentation, to help users get started with Lean and advance their understanding of formal proof.

To get started with Lean, refer to the Lean website (https://leanprover.github.io/) for installation instructions and documentation. The website also includes links to the Lean community, where users can ask questions, share ideas, and collaborate on formal proof projects.

In conclusion, Lean is a powerful and versatile theorem prover that combines programming and formal logic. It provides a rich set of tools for constructing and manipulating formal proofs, making it a valuable tool in mathematics and computer science.

```
  {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
```

隐式参数“motive”是正在定义的函数的陪域（codomain）。
在类型理论中，常常说“motive”是消除/递归的“动机”（motive），因为它描述了我们希望构造的对象的种类。
接下来的两个参数指定了如何计算零和后继情况，如上所述。它们也被称为“次要前提”（minor premises）。
最后，`t: Nat`是函数的输入。它也被称为“重要前提”（major premise）。

与`Nat.rec`类似，在`Nat.recOn`中，重要前提出现在次要前提之前。

```
@Nat.recOn :
  {motive : Nat → Sort u}
  → (t : Nat)
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → motive t
```

考虑一个例子，自然数上的加法函数 ``add m n``。固定``m``，我们可以通过对``n``进行递归定义来定义加法。在基本情况下，我们将``add m zero``设为``m``。在后继步骤中，假设值``add m n``已经确定，我们将``add m (succ n)``定义为``succ (add m n)``。

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
# end Hidden
```

将这样的定义放入一个命名空间 "Nat" 中是有用的。然后我们可以在该命名空间中定义熟悉的符号表示法。现在，加法的两个定义方程在定义上成立：

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#  deriving Repr
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
# end Hidden
```

我们将在[类型类章节](./type_classes.md)中解释 `instance` 命令的工作原理。在下面的示例中，我们将使用Lean的自然数版本。

然而，像 `zero + m = m` 这样的事实需要通过归纳来证明。如上所述，归纳原理只是递归原理的一个特例，当余域 `motive n` 是 `Prop` 的一个元素时。它表示了归纳证明的熟悉模式：要证明 `∀ n, motive n`，首先证明 `motive 0`，然后对任意的 `n`，假设 `ih : motive n` 并证明 `motive (succ n)`。

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc 0 + succ n
      _ = succ (0 + n) := rfl
      _ = succ n       := by rw [ih])
# end Hidden
```

请注意，在这里使用``Nat.recOn``实际上是使用了归纳原理。``rewrite`` 和 ``simp`` 策略在这类证明中往往非常有效。在这种情况下，可以使用这两种策略将证明简化为：

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
# end Hidden
```

作为另一个例子，让我们来证明加法的结合律，
``∀ m n k， m + n + k = m + (n + k)``。
（按照我们的定义，``+`` 是左结合的，所以 ``m + n + k`` 实际上是 ``(m + n) + k``。）
最困难的部分是确定选择哪个变量进行归纳。由于加法是根据第二个参数进行递归定义的，
我们可以选择 ``k`` 这个变量，一旦做出这个选择，证明几乎可以自己完成：

```lean
# namespace Hidden
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc m + n + succ k
        _ = succ (m + n + k)   := rfl
        _ = succ (m + (n + k)) := by rw [ih]
        _ = m + succ (n + k)   := rfl
        _ = m + (n + succ k)   := rfl)
# end Hidden
```

再一次地，您可以将证明简化为：

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih])
```

假设我们试图证明加法的交换性。选择对第二个参数为自然数的归纳法，我们可能开始如下：

```lean
theorem add_comm : ∀ (a b : ℕ), a + b = b + a :=
begin
  intro a, -- 第一步：引入假设a
  induction b with n hn, -- 第二步：对b使用归纳法，引入假设n和归纳假设hn
  -- base case: n = 0
  { -- 第三步: 处理基础情况n = 0
    rw [zero_add, add_zero], -- 步骤3.1：利用零元的定义，rewriting原目标
    -- 步骤3.2：原目标变为a+0=a
    rw [add_zero],
    -- 步骤3.3：目标已达到
  },
  -- induction step: suppose n holds
  { -- 第四步：处理归纳步骤，假设n成立
    rw [add_succ, succ_add, hn], -- 步骤4.1：应用归纳假设hn以及后继和加法的定义，rewriting原目标
    -- 步骤4.2：原目标变为a+(n+1)=(n+1)+a
    rw [succ_add],
    -- 步骤4.3：目标已达到
  }
end
```

这是一个使用 Lean 语言证明加法的交换性的示例。

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)
```

在这一点上，我们看到我们还需要另一个支持事实，即 "succ(n + m) = succ n + m"。
你可以通过对 "m" 进行归纳来证明这一点：

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)
```

你可以把前面证明中的 ``sorry`` 替换为 ``succ_add``。同样地，这些证明可以被压缩：

```lean
# namespace Hidden
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp [add_succ, succ_add, ih])
# end Hidden
```

其他递归数据类型
--------------------------

让我们考虑一些更多的归纳定义类型的例子。对于任何类型``α``，类型``List α``表示由``α``类型的元素组成的列表，在库中已经定义好了。

```lean
# namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
# end Hidden
```

一个类型为 ``α`` 的列表要么是空列表，即 ``nil``，要么是一个元素 ``h : α`` 后跟着一个列表 ``t : List α``。
第一个元素 ``h`` 常被称为列表的“头部”，而剩余的部分 ``t`` 则被称为列表的“尾部”。

作为一个练习，证明以下命题：

```lean
# namespace Hidden
# inductive List (α : Type u) where
# | nil  : List α
# | cons : α → List α → List α
# namespace List
# def append (as bs : List α) : List α :=
#  match as with
#  | nil       => bs
#  | cons a as => cons a (append as bs)
# theorem nil_append (as : List α) : append nil as = as :=
#  rfl
# theorem cons_append (a : α) (as bs : List α)
#                     : append (cons a as) bs = cons a (append as bs) :=
#  rfl
theorem append_nil (as : List α) : append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  sorry
# end List
# end Hidden
```

尝试定义函数 ``length : {α : Type u} → List α → Nat``，它返回一个列表的长度，
并证明它的行为是符合预期的（例如，``length (append as bs) = length as + length bs``）。

另一个例子是，我们可以定义二叉树的类型：

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

实际上，我们甚至可以定义可数分支树的类型：

在定义可数分支树之前，我们首先需要了解分支树的概念。分支树是一种有序的层级结构，它的每个节点可以有多个后继节点。一个节点的后继节点的数量被称为该节点的分支数。

根据这个概念，我们可以定义一个可数分支树为具有可数个分支数的树状结构。具体而言，我们可以定义一个可数分支树为满足以下条件的树状结构：

1. 树中的每个节点都有可数个后继节点。
2. 树中不存在无限循环的路径，即不存在一个节点的后继节点可以通过一系列的路径回到该节点本身。

根据这个定义，可数分支树可以具有无限的深度，因为每个节点都可以有无限个后继节点。

举个例子来说，考虑一个可数分支树，根节点有2个后继节点，每个后继节点又有3个后继节点，每个后继节点又有4个后继节点，以此类推。这个可数分支树就满足了定义中的条件。

通过定义可数分支树的类型，我们可以更好地理解并研究这类树状结构的特性和性质。

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

归纳类型的策略
---------------------------

鉴于归纳类型在 Lean 中的基本重要性，有一些策略旨在有效地与它们一起工作。我们在这里描述其中一些策略。

``cases`` 策略适用于归纳定义类型的元素，它完成了其名称所示的功能：根据每个可能的构造函数分解元素。在最基本的形式中，它被应用于局部上下文中的元素 ``x``。然后，它将目标减少为替换 ``x`` 为每个构造函数的情况。

```lean
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)
```

``cases``提供了一些额外的功能。首先，``cases``允许使用``with``子句为每个可选项选择名称。在下面的例子中，我们选择将参数``succ``命名为``m``，所以第二种情况引用的是``succ m``。更重要的是，cases策略会检测局部上下文中依赖目标变量的任何元素。它会撤消这些元素，进行分割，并重新引入它们。在下面的例子中，注意到假设``h : n ≠ 0``会变成第一个分支中的``h : 0 ≠ 0``，而在第二个分支中会变成``h : succ m ≠ 0``。

```lean
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl
```

注意到 ``cases`` 既可以用来证明命题，也可以用来生成数据。

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

再一次地，在这个背景下，案例将会恢复、分裂，并再次引入依赖关系。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

以下是一个带有多个带参数的构造函数的例子。

```java
public class Person {
    private String name;
    private int age;

    // 构造函数 1 - 接收姓名参数
    public Person(String name) {
        this.name = name;
    }

    // 构造函数 2 - 接收姓名和年龄参数
    public Person(String name, int age) {
        this.name = name;
        this.age = age;
    }

    // 获取姓名
    public String getName() {
        return name;
    }

    // 获取年龄
    public int getAge() {
        return age;
    }
}
```

此例中，`Person` 类具有两个构造函数。构造函数可通过传递不同的参数来创建不同的 `Person` 对象。

第一个构造函数接收一个参数 `name`，并将其赋值给类的 `name` 实例变量。这样，我们可以通过以下方式创建 `Person` 对象：

```java
Person person1 = new Person("John");
```

第二个构造函数接收两个参数 `name` 和 `age`，并分别将它们赋值给类的 `name` 和 `age` 实例变量。这样，我们可以通过以下方式创建 `Person` 对象：

```java
Person person2 = new Person("Jane", 25);
```

这两个构造函数允许我们根据不同的需求创建不同的 `Person` 对象。通过这种方式，我们可以方便地使用不同的参数来初始化对象。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

对于每个构造函数的替代方案，不需要按照声明的顺序解决。

```lean
# inductive Foo where
#   | bar1 : Nat → Nat → Foo
#   | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

``with`` 语法方便了结构化证明的编写。
Lean 还提供了一个补充的 ``case`` 策略，它允许您专注于目标并为变量命名。

```lean
# inductive Foo where
#   | bar1 : Nat → Nat → Foo
#   | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```

"case"策略非常巧妙，它可以将构造函数匹配到相应的目标。例如，我们可以按相反的顺序填充上面的目标:

```lean
# inductive Foo where
#   | bar1 : Nat → Nat → Foo
#   | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

你也可以使用``cases``命令处理任意表达式。假设该表达式出现在目标中，``cases``策略将对该表达式进行概括，引入相应的普遍量化变量，并对其进行分类讨论。

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)
```

将这个定理理解为在是否 ``m + 3 * k`` 是零或某个数的继任数两种情况下进行拆分。结果在功能上等价于以下内容：

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)
```

注意，表达式 ``m + 3 * k`` 被 ``generalize`` 擦除了；最重要的是它是 ``0`` 还是 ``succ a`` 的形式。这种形式的 ``cases`` 不会还原出包含在等式中提到这个表达式的任何假设。如果这样的术语出现在假设中，并且您希望同时对其进行概括，您需要显式地使用 ``revert`` 。

如果您对的情况不出现在目标中，``cases`` 策略将使用 ``have`` 将表达式的类型添加到上下文中。下面是一个例子：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

定理“``Nat.lt_or_ge m n``说的是“``m < n ∨ m ≥ n``”，很自然地将上述证明想象为对这两种情况进行拆分。在第一种情况下，我们有假设“``hlt : m < n``”，在第二种情况下，我们有假设“``hge : m ≥ n``”。上述证明在功能上等效于以下内容：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

在前两行之后，我们有假设 ``h ：m < n ∨ m ≥ n``，我们只需要对这个假设进行分情况讨论。

这里还有另一个例子，我们利用自然数的相等性可决定性来对情况 ``m = n`` 和 ``m ≠ n`` 进行划分。

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```

请记住，如果你 ``open Classical`` ，你可以对任何命题使用排中律。但是，使用类型类推断（参见[类型类章节](./type_classes.md)），Lean 实际上可以找到相关的决策过程，这意味着你可以在可计算的函数中使用 case split。

就像 "cases" 策略可以用来进行 Cases 证明一样，"induction" 策略可以用来进行归纳证明。其语法与 "cases" 类似，只是参数只能是局部环境中的项。以下是一个例子：

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

与``cases``一样，我们可以使用``case``策略来替代``with``。

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

以下是一些附加示例：

```lean
# namespace Hidden
# theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
# end Hidden
```

`induction` 策略还支持带有多个目标（也称为主前提）的用户自定义归纳原理。

```lean
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
```

在策略中也可以使用 `match` 表示法：

```coq
match goal with
| H: A /\ B |- _ => destruct H as [HA HB]
| H: A \/ B |- _ => destruct H as [HA | HB]
| H: ~ _ |- _ => apply False_ind, H
| _ => idtac
end.

match goal with
| |- A /\ B => split
| |- A \/ B => left; assumption
| |- ~ _ => intros Hcontra; contradiction
end.
```

这种 `match` 表示法允许我们根据目标的形式来选择不同的策略进行证明。在第一个 `match` 中，我们根据前提的形式将目标分为了四种情况。如果前提是 A /\ B，则我们可以使用 `destruct` 策略将其拆分为两个子前提 HA 和 HB；如果前提是 A \/ B，则我们可以使用 `destruct` 策略将其拆分为两个子前提 HA 或 HB；如果前提是 ~ P，则我们可以使用 `apply` 策略将目标转化为 False 类型，并应用前提 H；如果前提是其他形式，则什么也不做。在第二个 `match` 中，我们根据目标的形式选择不同的策略进行证明。如果目标是 A /\ B，则使用 `split` 策略将其拆分为两个子目标 A 和 B；如果目标是 A \/ B，则使用 `left; assumption` 策略选择左侧作为证明，并使用 `assumption` 策略来证明子目标 A 或 B；如果目标是 ~ P，则使用 `intros` 策略引入假设 Hcontra，并使用 `contradiction` 策略来得出矛盾。

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

为了方便起见，模式匹配已经集成到`intro`和`funext`等策略中。

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```

我们在本节中介绍最后一种策略，它旨在方便使用归纳类型，即 ``injection`` 策略。按设计，归纳类型的元素是自由生成的，也就是说，构造函数是单射的，且范围不相交。``injection`` 策略的设计就是为了利用这一事实：

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```

该策略的第一个实例将“h' : succ m = succ n”添加到上下文中，而第二个实例将“h'' : m = n”添加到上下文中。

``injection`` 策略还会检测到当不同的构造函数相等时产生的矛盾，并使用它们来关闭目标。

```lean
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

正如第二个例子展示的那样，``contradiction`` 策略也可以检测到这种形式的矛盾。

归纳家族
-------

我们几乎已经描述完 Lean 可接受的归纳定义的全部范围。到目前为止，您已经看到 Lean 允许您引入具有任意数量的递归构造器的归纳类型。实际上，单个归纳定义可以引入一个索引化的*家族*归纳类型，我们将在下面进行描述。

一个归纳家族是由以下形式的同时归纳定义所定义的索引化类型族：

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```

与普通的归纳定义不同，普通的归纳定义构造了某个 `Sort u` 的元素，而更一般的版本构造了一个函数 `... → Sort u`，其中 "``...``" 表示一系列参数类型，也被称为*指标*。然后，每个构造函数构造了一个家族成员的元素。一个例子是 `Vector α n` 的定义，它是长度为 `n` 的 `α` 元素向量类型：

```lean
# namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# end Hidden
```

注意，``cons`` 构造器接受一个属于 ``Vector α n`` 的元素，并返回一个属于 ``Vector α (n+1)`` 的元素，因此它使用了一个家族成员的元素来构建另一个成员的元素。

一个更为奇特的例子是 Lean 中等号类型的定义：

```lean
# namespace Hidden
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
# end Hidden
```

对于固定的 ``α : Sort u`` 和 ``a : α``，这个定义构造了一个类型族 ``Eq a x``，其中 ``x : α`` 是索引。
然而需要注意的是，这个类型族只有一个构造器，即 ``refl``，它是 ``Eq a a`` 的一个元素。
直观地说，构造 ``Eq a x`` 的证明的唯一方法是在 ``x`` 是 ``a`` 的情况下使用自反性。
需要注意的是，``Eq a a`` 是类型族 ``Eq a x`` 中唯一有元素的类型。
Lean 生成的消除原则如下：

```lean
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)
```

值得注意的是，所有关于相等性的基本公理都可以从构造子“refl”和消除子“Eq.rec”中推导出来。然而，相等性的定义是非典型的；请参阅[公理细节部分](#axiomatic-details)中的讨论。

消除子“Eq.rec”也用于定义替换：

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
# end Hidden
```

你还可以使用`match`定义`subst`。

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
# end Hidden
```

实际上，Lean 使用基于 `Eq.rec` 的定义来编译 `match` 表达式。

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst
  -- ... subst.match_1 ...
#print subst.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...
# end Hidden
```

使用递归器或 `match`，假设有 ``h₁ : a = b``，我们可以假设 ``a`` 和 ``b`` 是相同的，这样 ``p b`` 和 ``p a`` 也是相同的。

证明``Eq``是对称和传递的并不难。
在以下示例中，我们证明了``symm``，并将``trans``和``congr``（相容性）定理留为练习。

```lean
# namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
# end Hidden
```

在类型理论文献中，还有进一步的归纳定义的一般化，比如“归纳递归”和“归纳归纳”的原理。但这些并不被 Lean 支持。

公理细节
-----------------

我们已经通过例子描述了归纳类型及其语法。本节提供了关于公理基础的额外信息。

我们已经看到归纳类型的构造子接受“参数”（在归纳构造过程中保持不变的参数）和“索引”（参数化正在同时构造的类型族的参数）作为输入。每个构造子应该有一个类型，其中的参数类型是由之前定义的类型、参数和索引类型以及当前正在定义的归纳族类型构建起来的。要求是如果后者存在，则它仅以*严格正变形*的形式出现。这简单地意味着构造子中出现的任何与之相关的参数都是依赖箭头类型，其中正在定义的归纳类型仅作为结果类型出现，在其中索引以常数和前面的参数的形式给出。

由于归纳类型位于某个``Sort u``中，因此合理地询问``u``可以被实例化为哪个宇宙层级。定义一族归纳类型``C``中的每个构造子``c``的形式为

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

其中 ``a`` 是数据类型参数的序列，``b`` 是构造函数的参数序列，``p[a, b]`` 是索引，用于确定构造的元素属于归纳族中的哪个部分。（需要注意的是，这个描述有点误导性，因为构造函数的参数可以以任何顺序出现，只要依赖关系合理即可。）对于 ``C`` 的宇宙级别的约束分为两种情况，取决于归纳类型是否被指定为落在 ``Prop``（即 ``Sort 0``）中。

首先考虑归纳类型不指定落在 ``Prop`` 中的情况。那么宇宙级别 ``u`` 需要满足以下约束：

> 对于上述每个构造函数 ``c``，以及序列 ``β[a]`` 的每个 ``βk[a]``，如果 ``βk[a] : Sort v``，则有 ``u`` ≥ ``v``。

换句话说，宇宙级别 ``u`` 要求至少与表示构造函数参数的每个类型的宇宙级别一样大。

当归纳类型被指定为落在 ``Prop`` 中时，对于构造函数参数的宇宙级别没有约束。但是这些宇宙级别确实对消除规则有影响。一般来说，对于落在 ``Prop`` 中的归纳类型，消除规则的动机必须落在 ``Prop`` 中。

在最后一条规则中有一个例外：当只有一个构造函数，并且每个构造函数参数要么在 ``Prop`` 中，要么是一个指数时，我们可以将归纳定义的 ``Prop`` 逐步消除为任意 ``Sort``。直观上，这种情况下消除不需要使用任何除了类型被实例化之外的额外信息。这种特殊情况被称为*单例消除*。

我们已经在归纳定义的等式类型的``Eq.rec``使用中看到了单例消除的作用。我们可以使用元素``h : Eq a b``将元素``t' : p a``转换为``p b``，即使``p a``和``p b``是任意类型，
由于 cast 不生成新数据；它只是重新解释我们已经拥有的数据。单例消除也与异构相等和基于良基的递归一起使用，这将在《归纳和递归》一章中详细讨论。

相互和嵌套的归纳类型
--------------------------------

现在，我们考虑两个常用的归纳类型的一般化，Lean 通过将它们“编译”成上面描述的更原始的归纳类型来支持它们。换句话说，Lean 解析更一般的定义，基于它们定义辅助归纳类型，然后使用这些辅助类型来定义我们真正想要的类型。Lean 的等式编译器，将在下一章中描述，需要有效地使用这些类型。尽管如此，在这里描述这些声明是有意义的，因为它们是普通归纳定义的直接变体。

首先，Lean 支持 *相互定义的* 归纳类型。思想是我们可以同时定义两个（或更多）归纳类型，其中每个类型都引用其他类型。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

在这个例子中，同时定义了两种类型：自然数“n”是“Even”（偶数），如果它是“0”或者是一个“Odd”（奇数）加一，而且也是“Odd”（奇数），如果它是一个“Even”（偶数）加一。
在下面的练习中，你需要详细说明细节。

互相彼此的归纳定义也可以用来定义具有由“α”元素标记的节点的有限树的符号。

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```

根据这个定义，可以通过给出一个α类型的元素和一个可能为空的子树列表来构造一个``Tree α``的元素。子树列表由``TreeList α``类型表示，定义为空列表``nil``或者树和``TreeList α``的元素的``cons``。

然而，这个定义并不方便使用。如果子树列表由``List (Tree α)``类型给出，会更好，特别是因为Lean的库中包含了许多用于处理列表的函数和定理。可以证明``TreeList α``类型与``List (Tree α)``是*同构*的，但在这个同构之间来回转换结果很繁琐。

事实上，Lean允许我们定义真正想要的归纳类型：

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```

这被称为*嵌套*归纳类型。它不完全符合上一节中给出的归纳类型的严格规定，因为`Tree`在`mk`的参数中不是严格正向出现的，而是嵌套在`List`类型构造子中。Lean内核会自动在`TreeList α`和`List (Tree α)`之间建立同构，并基于同构定义`Tree`的构造函数。

练习
---------

1. 尝试定义其他关于自然数的运算，如乘法、前驱函数（满足`pred 0 = 0`）、截断减法（当`m`大于等于`n`时，`n - m = 0`）和指数运算。然后，尝试证明它们的一些基本性质，基于我们已经证明的定理。

   由于许多这些在Lean的核心库中已经定义好，您应该在一个名为"Hidden"的命名空间中工作，以避免名称冲突。

2. 定义一些关于列表的操作，如 `length` 函数或 `reverse` 函数。证明一些属性，比如以下的性质：

   a. `length (s ++ t) = length s + length t`

   b. `length (reverse t) = length t`

   c. `reverse (reverse t) = t`

3. 定义一个归纳数据类型，由以下构造子构建的项组成：

   - `const n`，表示自然数`n`的常数
   - `var n`，表示编号为`n`的变量
   - `plus s t`，表示`s`和`t`的和
   - `times s t`，表示`s`和`t`的乘积

   递归地定义一个函数，对于变量的赋值，可以计算出任何这样的项。

4. 同样，定义命题公式的类型，以及该类型上的函数：一个评估函数，度量公式复杂性的函数，以及用另一个给定的变量替换公式的函数。