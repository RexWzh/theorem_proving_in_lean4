与Lean的交互
=====================

您现在已经熟悉了依赖类型理论的基本知识，既作为定义数学对象的语言，也作为构建证明的语言。您唯一缺少的是定义新数据类型的机制。在下一章中，我们将填补这个空白，引入“归纳数据类型”的概念。但是首先，在本章中，我们暂时离开类型论的机制，探索与Lean交互的一些实用方面。

这里的信息并不都是对您立即有用的。我们建议您快速浏览本节以了解Lean的功能，并根据需要再回头查看。

导入文件
---------------

Lean的前端目标是解释用户输入，构造形式化表达式，并检查其形式是否正确。Lean还支持使用各种编辑器，提供持续的检查和反馈。更多信息可以在 [Lean文档页](https://leanprover.github.io/documentation/)上找到。

Lean标准库中的定义和定理分布在多个文件中。用户可能还希望使用其他库，或者跨多个文件开发自己的项目。当Lean启动时，它会自动导入``Init``文件夹中的库内容，其中包括一些基本定义和构造。因此，我们在这里介绍的大部分示例都可以直接使用。

但是，如果要使用其他文件，您需要手动导入它们，即在文件开头使用``import``语句。例如，命令

```
import data.nat.basic
```

导入了Lean的标准库中的``data.nat.basic``文件中的内容。

```
import Bar.Baz.Blah
```

引入文件 ``Bar/Baz/Blah.olean``，其中描述被解释为相对于 Lean 的 *搜索路径* 的路径。关于如何确定搜索路径的信息可以在[文档页](https://leanprover.github.io/documentation/)上找到。默认情况下，它包括标准库目录以及（在一些上下文中）用户本地项目的根目录。也可以指定相对于当前目录的导入；例如，导入是传递的。换句话说，如果你导入了 ``Foo`` 和 ``Foo`` 导入了 ``Bar``，那么你也可以访问 ``Bar`` 的内容，不需要显式导入它。

关于节的更多信息
----------------

Lean 提供了各种节区的机制来帮助结构化一个理论。你在[变量和节区](./dependent_type_theory.md#variables-and-sections)中看到，``section`` 命令不仅可以将理论的相关元素进行分组，还可以声明作为定义和定理的参数的变量，根据需要插入。请记住，“variable”命令的目的是声明用于定理的变量，如下面的例子所示：

```lean
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

"double"的定义不需要将"x"声明为参数；LEAN会自动检测到这种依赖并自动插入。同样，LEAN也会自动检测到在"t1"和"t2"中出现的"x"，并在那里自动插入。请注意，"double"的参数中没有"y"。变量仅在实际使用它们的声明中包含。

更多关于命名空间
--------------

在LEAN中，标识符由分层的*名称*表示，例如"Foo.Bar.baz"。在[命名空间](./dependent_type_theory.md#namespaces)中，我们看到LEAN提供了处理层级名称的机制。命令"namespace foo"会在每个定义和定理的名称前面加上"foo"，直到遇到"end foo"为止。然后，命令"open foo"会为以"foo"为前缀的定义和定理创建临时的*别名*。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar
```

下面是LEAN 定理证明定义的翻译:

##### **定义1.1 定理**
一个“定理”是一个希望通过具体推演来证明的断言。我们在一个解释内容的上下文中讨论定理，在这个上下文中，我们相信至少有一种方法可以根据定理是否正确的情况来评判。一个定理的“证明”是一个使定理被普遍接受的论据。

##### **定义1.2 命题**
一个“命题”是一个可以被证明为真或假的断言。在一段特定的解释内容的上下文中，我们可以根据命题是否正确对其进行判断。命题的证明是一个论据，通过该论据我们可以得出命题的真实性或虚假性。

##### **定义1.3 假设**
一个“假设”是一个我们暂时认为是真的断言，但我们并不确定它是否真实。当我们提出假设时，我们接受它的约束，并将其用于进一步的推理和论证。在证明中，我们会明确列出所有的假设，并在推理的每一步中采用恰当的假设。

##### **定义1.4 定理证明的结构**
一个定理证明由以下几个部分组成：

1. 证明的起点(基础)：一个证明的起点是一个已知的、被普遍接受的事实或真理，它不需要被证明。我们可以从一个证明的起点开始进行推理。
2. 步骤：一个证明是由一系列有条理的步骤组成的。每一步都使用推理规则将某个断言转化为另一个断言。每一步的正确性都可以被证明，并且必须根据前一步的结果建立。
3. 结论：一个证明的结论是一个表明定理确认为真的最后的断言。存在许多可能的推理路径可以得出同一个结论，但是在证明中我们只需要关注一个。

##### **定义1.5 推理规则**
推理规则是一种逻辑工具，用于在论证过程中从给定断言推导出新的断言。常见的推理规则包括引入和排除规则。推理规则必须合乎逻辑并且正确使用。

##### **定义1.6 证明的策略**
证明的策略是指在证明过程中应用的推理规则和方法。选择一个适当的策略是证明定理的关键。了解不同的策略和如何运用它们对于有效的证明是至关重要的。

##### **定义1.7 反证法**
反证法是一种证明方法，其中我们假设定理不成立，然后通过推理证明这个假设是不可行的。如果我们最终得出了一个矛盾的结论或违反已知事实的结果，则我们可以确定定理是成立的。

##### **定义1.8 归纳证明**
归纳证明是一种证明方法，其中我们首先证明一个断言在某个基础情形下成立，然后在递归地证明该断言在所有后续情形下也成立。归纳证明常用于处理具有可复制结构的问题，并且需要通过基础情形的推理来逐步扩展到更复杂的情形。

##### **定义1.9 直接证明**
直接证明是一种证明方法，其中我们根据定理的前提使用推理规则逐步推导出结论。直接证明通常是最常见和直观的证明方法之一。

##### *补充说明：*
上述定义和解释是根据 LEAN 定理证明的一些常见术语和概念进行描述。这些定义和概念为理解证明的结构和方法提供了基础。在实际应用中，根据具体问题的特点和要求，证明的方法和策略可能会有所不同。在进行定理证明时，确保逻辑正确性、严谨性和清晰性是非常重要的。

```lean
def Foo.bar : Nat := 1
```

在LEAN中，"LEAN"被视为一个宏，并展开为

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

尽管定理和定义的名称必须是唯一的，但用于标识它们的别名可以不唯一。当我们打开一个命名空间时，标识符可能是模糊的。Lean试图使用类型信息来消除上下文中的歧义，但您始终可以通过给出完整的名称来消除歧义。为此，字符串 ``_root_`` 是对空前缀的显式描述。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type
```

我们可以使用 ``protected`` 关键字阻止创建较短的别名：

```lean
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar
```

这通常用于像 ``Nat.rec`` 和 ``Nat.recOn`` 这样的名称，以防止常见名称的重载。

``open`` 命令允许多种变体。命令可以接受以下参数：

```lean
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3
```

创建仅对列出的标识符创建别名。命令

```lean
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3
```

在 ``Nat`` 命名空间中为除了所列标识符之外的所有内容创建别名。

```lean
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
```

创建别名把 ``Nat.mul`` 重命名为 ``times``，把 ``Nat.add`` 重命名为 ``plus``。

有时候从一个命名空间导出别名到另一个命名空间或顶层是很有用的。这个命令可以实现：

```lean
export Nat (succ add sub)
```

在当前命名空间中为 ``succ``，``add`` 和 ``sub`` 创建别名，以便在打开命名空间时可以使用这些别名。如果该命令在命名空间之外使用，则这些别名将导出到顶层命名空间。

属性
----------

Lean 的主要功能是将用户输入转换为形式化表达式，然后通过内核进行检查，最后存储在环境中以供以后使用。但是，一些命令对环境产生其他影响，例如为环境中的对象分配属性、定义符号表示法或声明类型类的实例，如 [Type Classes 章节](./type_classes.md) 中所述。这些命令大多具有全局影响，也就是说，它们不仅在当前文件中生效，而且在导入了该文件的任何文件中都生效。但是，这种命令通常支持 ``local`` 修饰符，表示它们仅在当前``section`` 或 ``namespace`` 关闭之前，或当前文件结束之前生效。

在 [Using the Simplifier 章节](./tactics.md#using-the-simplifier) 中，我们看到定理可以使用 ``[simp]`` 属性进行注释，这样它们就可以被简化器使用。下面的例子定义了列表上的前缀关系，证明了该关系是自反的，并将 ``[simp]`` 属性赋予了该定理。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

之后，简化器通过将 ``isPrefix [1, 2, 3] [1, 2, 3]`` 重写为 ``True`` 来证明它。

也可以在定义之后的任何时候分配属性：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

在所有这些情况下，属性在引入声明所在文件的任何文件中都保持有效。添加``local``修饰符限制了作用域：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp
```

另一个例子中，我们可以使用 `instance` 命令将符号 `≤` 赋予关系 `isPrefix`。该命令将在 [第10章 类型类](./type_classes.md) 中详细解释，它通过向关联的定义添加一个 `[instance]` 属性来实现。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

该定理的证明也可以是本地的：

```md
**定理：LEAN 定理证明可以在本地完成。**

*证明：*
为了证明这个定理，我们需要展示一个本地证明的步骤。假设我们有一个 LEAN 环境设置在我们的本地计算机上。

1. 在本地计算机上安装 LEAN 环境。可以从 LEAN 的官方网站下载并按照说明进行安装。

2. 创建一个 LEAN 项目。可以使用 LEAN 提供的命令行工具 `leanproject` 来创建一个新的项目。

3. 在项目中创建一个新的 LEAN 文件并命名为 `proof.lean`。

4. 在 `proof.lean` 文件中，导入需要用到的 LEAN 库。

   ```lean
   import tactic
   ```

5. 添加一个定理声明并给定其名称和陈述。例如：

   ```lean
   theorem my_theorem : 1 + 1 = 2 :=
   begin
     sorry
   end
   ```

   这个定理声明声明了 "1 + 1 = 2"。

6. 编写证明脚本。使用 tactic 编写证明脚本的过程类似于将传统的数学证明转化为形式化证明的步骤。例如：

   ```lean
   theorem my_theorem : 1 + 1 = 2 :=
   begin
     exact rfl
   end
   ```

   这个证明脚本使用了 `exact rfl` 来表示证明是显然的。

7. 运行 LEAN 环境中的验证器。使用 LEAN 提供的命令行工具 `lean` 来验证证明脚本的正确性。

8. 如果验证通过，那么我们成功地在本地完成了 LEAN 定理证明。如果验证失败，可以根据错误提示进行修正。

因此，我们证明了该定理可以在本地完成，只需在本地计算机设置 LEAN 环境并按照上述步骤进行操作即可。
```

通过以上步骤，我们证明了该定理可以在本地完成。

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#   ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
```

在下面的 [注释](#notation) 部分，我们将讨论 Lean 的定义符号的机制，并且可以看到它们也支持 ``local`` 修饰符。然而，在 [设置选项](#setting-options) 部分中，我们将讨论 Lean 的设置选项的机制，它不遵循这个模式：选项**只能**在局部范围内进行设置，也就是说，它们的作用域始终限定在当前节或当前文件中。

更多关于隐含参数
-----------

在 [隐含参数](./dependent_type_theory.md#implicit-arguments) 部分中，我们看到如果 Lean 将一个项 ``t`` 的类型显示为 ``{x : α} → β x``，那么花括号表示 ``x`` 已被标记为 *隐含参数*。这意味着每当你写下 ``t`` 时，会插入一个占位符或者说“空洞”，这样 ``t`` 就会被替换为 ``@t _``。如果你不希望这样发生，你必须写成 ``@t``。

请注意，隐含参数会被急切地插入。假设我们定义一个带有如上所示参数的函数 ``f (x : Nat) {y : Nat} (z : Nat)``。然后，当我们不带其他参数写出表达式 ``f 7`` 时，它将被解析为 ``f 7 _``。Lean 提供了一个更弱的注解 ``{{y : Nat}}``，它指定一个占位符只能在后续的显式参数之前添加。这个注解还可以用 ``⦃y : Nat⦄`` 的形式来写，其中 unicode 括号分别键入为 ``\{{`` 和 ``\}}``。使用这个注解，表达式 ``f 7`` 将被解析为原样，而 ``f 7 3`` 将被解析为 ``f 7 _ 3``，正如使用强注解时一样。

为了说明这种差异，考虑下面的例子，它展示了一个自反的欧几里得关系既是对称的又是传递的。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 @th2 _ _ (@th1 _ _ reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
```

结果被分解为以下几个小步骤：``th1`` 证明了一个既是反身性又是欧几里得性的关系是对称的，而 ``th2`` 证明了一个既是对称性又是欧几里得性的关系是传递的。然后 ``th3`` 结合了这两个结果。但请注意，我们必须手动禁用 ``th1``、``th2`` 和 ``euclr`` 中的隐式参数，否则会插入太多的隐式参数。如果使用弱隐式参数，问题将得到解决：

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r
```

有一种隐式参数用方括号 ``[`` 和 ``]`` 表示，它们用于类型类，如在[类型类章节](./type_classes.md)中所解释的。

表示法
--------

Lean 中的标识符可以包含任何字母数字字符，包括希腊字符（除了 ∀ , Σ 和 λ ，它们在依赖类型理论中有特殊含义）。它们还可以包含下标，在输入所需的下标字符之后输入 ``\_``。

Lean 的解析器是可扩展的，也就是说，我们可以定义新的表示法。

Lean 的语法可以在每个级别上由用户进行扩展和定制，从基本的“mixfix”表示法到定制的展开器。实际上，所有内置的语法都是使用相同的机制和 API 进行解析和处理的。在本节中，我们将描述和解释各种扩展点。

虽然引入新的表示法在编程语言中是相对少见的特性，有时甚至因其可能模糊代码而受到批评，但它是形式化的无价工具，可以简洁地表示所述领域的已建立惯例和表示法。超越基本表示法，Lean 的能力通过 (行为良好的) 宏将常见的样板代码分解出来，并嵌入整个定制的领域专用语言（DSL）来以文本方式高效和可读地编码子问题，可以极大地有益于程序员和证明工程师。

### 表示法和优先级

最基本的语法扩展命令允许引入新的（或重载现有的）前缀、中缀和后缀运算符。

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
# set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

在描述运算符类型（其 "结合性"）的初始命令名称后，我们给出了由冒号 `:` 隔开的运算符的 *解析优先级*，然后是用双引号括起的新的或现有的标记（空格用于漂亮的打印），然后是箭头 `=>` 后该运算符应该转换为的函数。

优先级是一个自然数，描述运算符与其参数的"紧密程度"，编码了操作的顺序。我们可以通过查看上述展开的命令来更清楚地说明这一点：

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

原来，第一个代码块中的所有命令实际上都是将更通用的 `notation` 命令转换为命令 *宏*。我们将在下面学习如何编写这样的宏。`notation` 命令不仅接受单个令牌，还接受带有优先级的令牌序列和命名的术语占位符，这些占位符可以在 `=>` 的右侧引用，并将被在那个位置解析的相应术语替换掉。具有优先级 `p` 的占位符只接受至少在该位置具有优先级 `p` 的记法。因此，字符串 `a + b + c` 不能被解析为等同于 `a + (b + c)`，因为 `infixl` 记法的右手操作数的优先级比记法本身大 1。相反，`infixr` 使用记法的优先级作为右手操作数的优先级，因此 `a ^ b ^ c` *可以* 被解析为 `a ^ (b ^ c)`。请注意，如果我们直接使用 `notation` 来引入中缀记法，例如

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

当优先级无法足够确定结合性时，Lean 的解析器将默认为右结合性。更准确地说，当存在歧义的文法时，Lean 的解析器遵循本地的*最长解析*规则：在解析 `a ~` 中的右侧时，在当前优先级允许的情况下，它将继续解析，不仅停留在 `b`，还会解析 `~ c`。因此，该术语等价于 `a ~ (b ~ c)`。

如上所述，`notation` 命令允许我们自由地定义任意的*混合采用*语法，可以自由地混合标记和占位符。

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

如果两个符号重叠，我们再次应用最长的解析规则：

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

Lean中，自然数类型``Nat``与整数类型``Int``不同。但是有一个名为``Int.ofNat``的函数，它将自然数嵌入整数中，也就是说我们可以在需要时将任何自然数视为整数。Lean有机制来检测和插入这种类型的*强制转换*。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

显示信息
----------------------

有多种方式可以查询 Lean 的当前状态以及当前上下文中可用的对象和定理的信息。你已经见过其中两种最常见的方式，``#check`` 和 ``#eval``。请记住，``#check`` 通常与 ``@`` 运算符一起使用，该运算符使定理或定义的所有参数显式。此外，你还可以使用 ``#print`` 命令来获取有关任何标识符的信息。如果标识符表示定义或定理，Lean 将打印符号的类型和定义。如果它是一个常量或一个公理，Lean 将指示这个事实，并显示类型。

```lean
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
```

设置选项
-----

Lean维护了许多内部变量，用户可以通过设置这些变量来控制其行为。设置语法如下所示：

```
set_option <name> <value>
```

一组非常有用的选项可以控制 Lean 的 *pretty-printer* 显示项的方式。以下选项接受 true 或 false 作为输入：

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

作为一个例子，以下设置会产生更长的输出：

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

命令“``set_option pp.all true``”一次性进行了这些设置，而“``set_option pp.all false``”则恢复到先前的值。在调试证明或理解晦涩的错误信息时，Pretty Printing（美化输出）附加信息通常非常有用。然而，太多的信息可能会让人不知所措，在普通交互中，Lean的默认设置通常就足够了。

<!--
扩展提示
-----------------

当你要求Lean处理表达式，例如``λ x y z, f (x + y) z``，你会隐含一些信息。例如，``x``，``y``和``z``的类型必须从上下文中推断出来，符号``+``可能是重载的，并且``f``可能有一些需要填入的隐式参数。而且我们将在 :numref:`第%s章 <type_classes>` 中看到，一些隐式参数是通过一种称为“类型类解析”（*type class resolution*）的过程来合成的。我们也在上一章中已经看到，一些表达式的部分可以通过策略框架来构造。

推断一些隐式参数是很直接的。例如，假设函数``f``的类型是``Π {α : Type*}, α → α → α``，而Lean正在尝试解析表达式``f n``，其中``n``可以被推断为类型``nat``。那么，隐式参数``α``就必须是``nat``。然而，某些推断问题是*高阶的*。例如，等式的替换操作``eq.subst``具有以下类型：

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

现在假设我们给出了``a b : ℕ``和``h₁ : a = b``和``h₂ : a * b > a``。那么，在表达式``eq.subst h₁ h₂``中，``p``可以是以下任何一个：

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

换句话说，我们的意图可能是要替换``h₂``中的第一个或第二个``a``，或者两者都替换，或者都不替换。在推断归纳谓词或推断函数参数时也会出现类似的歧义。甚至第二阶单一化已知是不可判定的。因此，Lean依靠启发式方法来填充此类参数，当它无法猜测出正确参数时，需要显式提供。
更糟糕的是，有时需要展开定义，有时需要根据底层逻辑框架的计算规则进行表达式约简。这时，Lean不得不依靠启发式算法来确定何时展开或者约简。

然而，有一些属性可以用来向展开器提供一些提示。其中一类属性确定了定义的展开程度：常量可以用属性“[reducible]”、“[semireducible]”或“[irreducible]”标记。定义默认被标记为“[semireducible]”。带有“[reducible]”属性的定义会被立即展开；如果你将定义视为缩写，那么这个属性是合适的。展开器避免展开带有“[irreducible]”属性的定义。定理默认被标记为“[irreducible]”，因为通常证明与展开过程无关。

值得强调的是，这些属性只是对展开器的提示。在检查展开后的项的正确性时，Lean的内核会展开它需要展开的所有定义。与其他属性一样，上述属性可以使用“local”修饰符，这样它们只在当前章节或文件中生效。

Lean还有一族属性来控制推导策略。一个定义或定理可以被标记为“[elab_with_expected_type]”、“[elab_simple]”或“[elab_as_eliminator]”。当应用于一个定义“f”时，这些属性影响到应用于参数的表达式“f a b c ...”的推导过程。默认情况下，使用“[elab_with_expected_type]”属性，参数“a”、“b”、“c”等根据它们的期望类型进行推导，该类型可以从“f”和前面的参数推断出来。相反，使用“[elab_simple]”属性，参数从左到右进行推导，不传播它们的类型信息。最后一个属性“[elab_as_eliminator]”通常用于递归器、归纳原理和“eq.subst”等消去器。它使用一个单独的启发式算法来推断高阶参数。我们将在下一章节中详细讨论这类操作。

这些属性可以在定义后进行赋值和重新赋值，你可以使用“local”修饰符限定它们的作用范围。此外，在表达式中在一个标识符前加上“@”符号会让展开器使用“[elab_simple]”策略；这样做的想法是，当你显式提供复杂的参数时，你希望展开器更加重视这些信息。实际上，Lean提供了另一种注解“@@”，它使得第一个高阶参数之前的参数保持隐式。例如，“@@eq.subst”使得等式的类型隐式，但是让替换的上下文变得显式。
使用库
-----------------

要有效地使用 Lean，您将不可避免地需要使用库中的定义和定理。回想一下，在文件开头的 ``import`` 命令可以导入其他文件中先前编译的结果，并且导入是可传递的；如果您导入 ``Foo``，而 ``Foo`` 导入了 ``Bar``，那么 ``Bar`` 的定义和定理也就会对您可用。但打开一个命名空间的操作，提供了更短的名称，这种操作不会传递。在每个文件中，您需要打开您希望使用的命名空间。

一般来说，您需要熟悉库及其内容，这样您就会知道有哪些定理、定义、符号和资源可供您使用。下面我们将看到，Lean 的编辑器模式也可以帮助您找到所需的内容，但是直接研究库的内容往往是不可避免的。Lean 的标准库可以在网上找到，位于 GitHub 上：

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)
- [https://github.com/leanprover/std4/tree/main/Std](https://github.com/leanprover/std4/tree/main/Std)

您可以使用 GitHub 的浏览器界面查看这些目录和文件的内容。如果您在自己的计算机上安装了 Lean，可以在 ``lean`` 文件夹中找到库，并通过文件管理器进行探索。每个文件顶部的注释标头提供了额外的信息。

Lean 的库开发人员遵循通用的命名准则，以便更容易猜出您所需的定理的名称，或者在支持此功能的 Lean 模式编辑器中使用制表符补全来找到它，这将在下一节中讨论。标识符通常是 `camelCase`，类型是 `CamelCase`。对于定理名称，我们依赖于描述性的名称，其中不同的组件由 `_` 分隔：

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

在 Lean 中，标识符可以组织成层次化的命名空间。例如，命名空间 ``Nat`` 中名为 ``le_of_succ_le_succ`` 的定理的完整名称为 ``Nat.le_of_succ_le_succ``，但通过命令 ``open Nat``（对于未标记为 `protected` 的名称）可以使用较短的名称。我们将在[归纳类型章节](./inductive_types.md)和[结构体和记录章节](./structures_and_records.md)中看到，在 Lean 中定义结构体和归纳数据类型会生成相关的操作，并且这些操作存储在与定义类型同名的命名空间中。例如，乘积类型带有以下操作：

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

第一个用于构造一对，而后两个 `Prod.fst` 和 `Prod.snd` 用于分别投射两个元素。最后一个 `Prod.rec` 提供了另一种机制，可以根据两个组件上的一个函数来定义关于产品上的函数。像 `Prod.rec` 这样的名称是 *protected* 的，这意味着即使 `Prod` 命名空间打开，仍然必须使用完整的名称。

通过命题作为类型的对应关系，逻辑连词也是归纳类型的实例，因此我们也倾向于对它们使用点符号表示法：

```lean
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
```

自动绑定隐式参数
--------------

在前一节中，我们展示了隐式参数如何使函数的使用更方便。然而，像 `compose` 这样的函数仍然很冗长。请注意，本节中的宇宙多态 `compose` 比之前定义的版本还要冗长。

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

你可以在定义 `compose` 时提供宇宙参数来避免使用 `universe` 命令。

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

Lean 4 支持一项名为*auto bound implicit arguments*的新功能。它使得像`compose`这样的函数更加方便地编写。当 Lean 处理声明的头部时，任何未绑定的标识符如果是一个单个小写字母或希腊字母，它将自动添加为隐式参数。有了这个特性，我们可以将`compose`写成下面这样：

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

请注意，Lean 使用 `Sort` 而不是 `Type` 推断出更一般的类型。

尽管我们喜欢这个功能，并且在实现 Lean 时广泛使用它，
但我们意识到一些用户可能对此感到不舒服。因此，您可以使用命令 `set_option autoImplicit false` 来禁用它。

```lean
set_option autoImplicit false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

隐式 Lambda 函数
---------------

在 Lean 3 的标准库中，我们经常会遇到可怕的 `@`+`_` 的写法的[实例](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39)。这种写法通常用于期望类型是带有隐式参数的函数类型，并且我们有一个同样带有隐式参数的常量（例如在示例中的 `reader_t.pure`）。在 Lean 4 中，解析器会自动引入 Lambda 函数来消耗隐式参数。我们仍在探索此功能并分析其影响，但到目前为止，体验非常积极。以下是使用 Lean 4 隐式 Lambda 函数的上述链接中的示例。

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

用户可以通过使用 `@` 或在 lambda 表达式中使用 `{}` 或 `[]` 的 binder 注释来禁用隐式 lambda 功能。以下是一些示例:

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

对于简单函数的糖语法
-------------------------

在 Lean 3 中，我们可以使用括号将中缀运算符转化为简单函数。例如，`(+1)` 是 `fun x, x + 1` 的一种糖语法。在 Lean 4 中，我们使用 `·` 作为占位符来推广这种表示法。下面是几个例子：

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

与Lean 3中一样，符号需要用括号激活，并且通过收集嵌套的 `·` 来创建 lambda 抽象。收集过程会被嵌套的括号打断。在下面的例子中，会创建两个不同的 lambda 表达式。

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

命名参数
---------------

命名参数让您可以通过与其在参数列表中的位置相匹配而不是位置指定参数的值。如果您不记得参数的顺序但知道它们的名称，您可以以任何顺序发送参数。您还可以在 Lean 无法推断参数的值时为隐式参数提供值。命名参数还通过标识每个参数表示的内容来提高代码的可读性。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

在下面的例子中，我们将说明命名参数和默认参数之间的交互作用。

```python
def greet(name, greeting='Hello'):
    print(f"{greeting}, {name}!")

# 通过位置参数调用函数
greet('Alice')
# 输出: Hello, Alice!

# 通过命名参数调用函数
greet(greeting='Hi', name='Bob')
# 输出: Hi, Bob!

# 结合使用位置参数和命名参数
greet('Charlie', greeting='Hey')
# 输出: Hey, Charlie!
```

在上面的示例中，我们定义了一个名为 `greet` 的函数，它接受两个参数 `name` 和 `greeting`，其中 `greeting` 的默认值为 `'Hello'`。当我们调用这个函数时，可以根据位置或名称提供参数的值。

第一个示例中，我们只提供了一个位置参数 `'Alice'`，因此函数会使用默认的 `greeting` 值 `'Hello'`，输出结果为 `'Hello, Alice!'`。

第二个示例中，我们使用了命名参数来调用函数，即通过指定参数的名称来提供参数的值。在这种情况下，我们通过 `'Hi'` 和 `'Bob'` 分别为 `greeting` 和 `name` 参数提供了值，输出结果为 `'Hi, Bob!'`。

第三个示例中，我们展示了如何结合使用位置参数和命名参数。我们通过位置参数 `'Charlie'` 为 `name` 参数提供了值，同时通过命名参数 `greeting='Hey'` 为 `greeting` 参数提供了值，输出结果为 `'Hey, Charlie!'`。

通过这些示例，我们可以看到名为 `greet` 的函数如何利用命名参数和默认参数的交互作用，使得函数调用更加灵活和易读。

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

您可以使用 `..` 作为 `_` 提供缺少的显式参数。
此功能与命名参数结合使用，非常适用于模式匹配。以下是一个例子：

```lean
def foo (x y z : ℕ) : ℕ :=
x + y + z

def bar : ℕ :=
let args : Σ'(x y z : ℕ), x = y ∧ y = z := ⟨2, _, _⟩,
    ⟨x, y, z⟩ := args in
foo x y z

#reduce bar -- 6
```

在这个示例中，我们定义了 `foo` 函数，该函数接受三个自然数参数 `x`、`y` 和 `z`，并返回它们的总和。然后我们定义了 `bar` 函数，它使用命名参数的优势在调用 `foo` 时仅提供了部分参数。`args` 是一个 `Σ'` 类型的变量，它具有类型 `(x y z : ℕ), x = y ∧ y = z`，即它包含了一个自然数三元组以及两个相等的条件。通过使用 `_`，我们省略了 `args` 的 `y` 和 `z` 参数。然后，我们解构 `args` 并将 `x`、`y` 和 `z` 绑定到其对应的值上。最后，我们调用 `foo` 函数，并传递解构出的参数 `x`、`y` 和 `z`。最终，我们通过 `#reduce` 验证了 `bar` 函数的输出结果为 6。

这个示例展示了 Lean 的 `..` 和命名参数的强大功能，通过使用这些特性，我们可以在编写模式时更加灵活和简洁。

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | add    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

当 Lean 能够自动推断出明确的参数时，省略号也是很有用的，这样我们就可以避免使用一系列的 `_`。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```

