依赖类型理论
=====================

依赖类型理论(dependent type theory) 是一种强大和表达力强的语言，您可以在其中表达复杂的数学断言，编写复杂的硬件和软件规范，并以一种自然和统一的方式进行推理。Lean 基于一种称为 “构造计算(Calculus of Constructions)” 的依赖类型理论的版本，其中有一个可数层次的非累积宇宙和归纳类型。通过本章的学习，您将对这些内容有深入的了解。

## 简单类型理论

“类型论”得名于**每个表达式都有一个关联的 *类型***。例如，在给定的上下文中，``x + 0`` 可能表示一个自然数，而 ``f`` 可能表示自然数上的函数。对于那些喜欢精确定义的人来说，Lean 中的自然数是一个任意精度的无符号整数。

下边看几个例子。与通常语言不同，LEAN 代码要在编辑器中打开（比如vscode），形如 ``#check `` 这类命令的结果将在右侧交互界面展示。显示方便，我们将结果放在注释 `--` 后边。

```lean
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

位于 ``/-`` 和 ``-/`` 之间的文本被视为注释块，Lean 会忽略它们。同样，两个短横线 `--` 表示该行剩余部分是注释，也会被忽略。注释块可以嵌套，这样可以像许多编程语言一样“注释掉”代码块。

``def`` 关键字将新的常量符号声明到工作环境中。在上面的示例中，`def m : Nat := 1` 定义了一个名为 `m` 的类型为 `Nat` 的新常量，其值为 `1`。``#check`` 命令要求 Lean 报告它们的类型；在 Lean 中，查询系统信息的辅助命令通常以井号（#）符号开头。`#eval` 命令要求 Lean 计算给定的表达式。你可以自己尝试定义一些常量和表达式进行类型检查。

简单类型理论的强大之处在于你可以用其他类型组合出新的类型。例如，如果 ``a`` 和 ``b`` 是类型，``a -> b``表示从 ``a`` 到 ``b`` 的函数类型，``a × b`` 表示由 ``a`` 元素和 ``b`` 元素组成的类型，也被称为 *笛卡尔积* 。注意，`×` 是一个 Unicode 符号。合理使用 Unicode 可以提高可读性，而且所有现代编辑器都支持。在Lean 标准库中，经常使用希腊字母表示类型，比如使用 Unicode 符号 `→` 作为 `->` 的更紧凑版本。

```lean
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

让我们来看一些基本的语法。在 vscode 中可以通过输入 ``\to`` 或 ``\r`` 或 ``\->`` 来插入 Unicode 箭头 ``→``。你也可以使用ASCII替代形式 ``->``，因此表达式 ``Nat -> Nat`` 和 ``Nat → Nat`` 的意思是相同的。这两个表达式都表示将自然数作为输入并返回自然数作为输出的函数类型。使用 Unicode 符号 ``×`` 表示笛卡尔积，输入方式为 ``\times``。通常你会使用小写希腊字母 ``α``、``β`` 和 ``γ`` 来表示类型的范围。你可以使用 ``\a``、``\b`` 和``\g`` 输入这些特定的字母。

这里还有一些需要注意的地方。首先，函数 ``f`` 应用到值 ``x`` 的表示方式是 ``f x``（例如，`Nat.succ 2`）。其次，在编写类型表达式时，箭头满足右结合率；例如，``Nat.add`` 的类型是 ``Nat → Nat → Nat``，它等同于 ``Nat → (Nat → Nat)``。因此，你可以将 ``Nat.add`` 看作是一个接受自然数并返回另一个接受自然数并返回自然数的函数。在类型理论中，这通常比将 ``Nat.add`` 编写为接受一对自然数作为输入并返回自然数作为输出的函数更方便。例如，它允许你对函数 ``Nat.add`` 进行“部分应用”(partial apply)，也就是[柯里化](https://en.wikipedia.org/wiki/Currying)。上面的示例说明了 ``Nat.add 3`` 的类型是 ``Nat → Nat``，也就是说，``Nat.add 3``返回一个“等待”第二个参数 ``n`` 的函数，等价于 ``Nat.add 3 n``。

> 通过柯里化，多参函数分解为单参函数的复合。
<!-- 将类型为``Nat × Nat → Nat``的函数``h``“重定义”为``g``是一种称为*柯里化*的过程。 -->

你已经看到，如果有 ``m : Nat`` 和 ``n : Nat``，那么 ``(m, n)`` 表示 ``m`` 和 ``n`` 的有序对，其类型为 ``Nat × Nat``。这样可以创建一对自然数。反过来，如果你有 ``p: Nat × Nat``，那么你可以写成 ``p.1: Nat`` 和 ``p.2: Nat``。这样可以提取出它的两个组成部分。

## 类型作为对象

Lean 的依赖类型理论扩展了简单类型理论的一种方法是，类型本身——如 ``Nat`` 和 ``Bool`` ——也是一等公民，也就是说它们本身也是对象。为了实现这一点，它们每一个也必须有一种类型。

> 函数式编程语言中，函数是“一等公民”，可以当做变量进行传值和运算。而在 LEAN 中，类型也是“一等公民”，可以进行 `×, →, ⊕` 之类的运算。

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

你可以看到上面每个表达式都是一个 `Type` 类型的对象。你还可以声明新的类型常量：

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

正如上面的例子所示，您已经看到了一个类型为 ``Type → Type → Type`` 的函数的实例，即笛卡尔积 `Prod`：

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

这是另一个例子：给定任何类型 ``α``，类型 ``List α`` 表示类型 ``α`` 元素的列表的类型。

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

鉴于 Lean 中的每个表达式都有一种类型，自然而然的是问：``Type`` 本身有什么类型？

```lean
#check Type      -- Type 1
```

您实际上已经遇到了 Lean 类型系统中最微妙的一个方面。Lean 的基础底层具有无限层次的类型：

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

将 ``Type 0`` 看作“小型”或“普通”类型的宇宙。``Type 1`` 则是一个更大的类型宇宙，它包含 ``Type 0`` 作为一个元素，而 ``Type 2`` 是一个更大的类型宇宙，它包含 ``Type 1`` 作为一个元素。列表是无限的，所以对于每个自然数 ``n``，都有一个 ``Type n``。``Type`` 是 ``Type 0`` 的缩写：

```lean
#check Type
#check Type 0
```

以下的表格可能有助于具体说明所讨论的关系。

沿着 x 轴的运动代表了宇宙的变化，而沿着 y 轴的运动代表了所谓的“度”的变化。左侧更加具体，右侧逐渐抽象。

|        |               |               |                 |                        |     |
|:------:|:-------------:|:-------------:|:---------------:|:----------------------:|:---:|
| sort   | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
| type   | True          | Bool          |   Nat -> Type   | Type -> Type 1         | ... |
| term   | trivial       | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |

然而，一些操作需要对类型宇宙进行 *多态(polymorphic)* 处理。例如，``List α`` 应该对于任何类型 ``α`` 都有意义，无论 ``α`` 位于哪个类型宇宙中。这也解释了函数 ``List`` 的类型注释：

```lean
#check (List)    -- Type u_1 → Type u_1
```

在这里，``u_1`` 是一个范围在类型级别上的变量。``#check`` 命令的输出表明，只要 ``α`` 具有类型 ``Type n``，那么``List α`` 也具有类型 ``Type n``。函数 ``Prod`` 同样是多态的：

```lean
#check Prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

要定义多态常量，Lean 允许你使用 `universe` 命令来显式地声明宇宙变量：

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

这是定义函数的语法，比如 ``def addone (n : Nat) : Nat := n + 1``，中间冒号左侧为参数，右侧为返回值类型，`:=` 右侧为表达式内容。

当定义 F 时，您可以通过提供宇宙参数来避免使用显式使用 `universe` 命令。

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

## 函数抽象与求值

Lean 提供了 `fun`（或 `λ` ）关键字来从表达式中创建一个匿名函数，如下所示：

```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
```

您可以通过传递所需的参数来对 lambda 函数求值：

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

将另一个表达式创建为函数的过程称为 *lambda抽象(lambda abstraction)* 。假设您有变量 ``x : α``，并且可以构建表达式 ``t : β``，那么表达式 ``fun (x : α) => t``，或等价地说，``λ (x : α) => t``，是类型为 ``α → β`` 的对象。可以将其视为从 ``α`` 到 ``β`` 的函数，将任何值 ``x`` 映射到值 ``t``。

以下三种写法等价

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

Lean 将最后三个例子解释为相同的表达式；在最后一个表达式中，Lean 从表达式 “如果不是 `y`，则 `x + 1`，否则 `x + 2` “中推断出 `x` 和 `y` 的类型。显式的写法：

```lean
def f (x : Nat) (y : Bool) : Nat := if not y then x + 1 else x + 2
-- def f x y := if not y then x + 1 else x + 2
#check f -- Nat → Bool → Nat
```

一些常见的函数操作示例：

```lean
def f (n : Nat) : String := toString n -- 数字转字符串
def g (s : String) : Bool := s.length > 0 -- 字符串转 bool

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

思考一下这些表达式的含义。表达式 ``fun x : Nat => x`` 代表了 ``Nat`` 上的恒等函数，表达式 ``fun x : Nat => true`` 代表了始终返回 ``true`` 的常数函数，而 ``fun x : Nat => g (f x)`` 代表了 ``f`` 和 ``g`` 的复合函数。通常情况下，你可以省略类型注释，让 Lean 来自动推断。因此，例如，你可以写成 ``fun x => g (f x)`` 而不是 ``fun x : Nat => g (f x)``。

你可以将函数作为参数传递，定义一个接收函数 `f, g` 并返回 `g` 和 `f` 的复合函数的函数：

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

您还可以将类型作为参数传递：

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```

λ 表达式的一般形式是 ``fun x : α => t``，其中变量 ``x`` 是一个“绑定变量”：它实际上是一个占位符，其“作用域”不延伸到表达式 ``t`` 之外。例如，表达式 ``fun (b : β) (x : α)=> b`` 中的变量 ``b`` 与之前声明的常量 ``b`` 无关。事实上，该表达式表示与 ``fun (u : β) (z : α)=> u`` 相同的函数。

形式上，对于通过重新命名绑定变量可以相同的表达式称为 “*alpha等价*”，并被认为是“相同的”，Lean 识别这种等价性。

注意，将项 ``t : α → β`` 应用到项 ``s : α`` 上会得到一个表达式 ``t s : β``。回到前面的例子并为了清晰起见对绑定变量重新命名，注意以下表达式的类型：

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

如预期，表达式 ``(fun x : Nat =>  x) 1`` 的类型是 ``Nat``。
事实上，更多的是这样：将表达式 ``(fun x : Nat => x)`` 应用于 ``1`` 应该会“返回”值 ``1``。而且，的确如此：

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

你将会看到这些术语是如何求值的。现在，请注意，这是依赖类型理论的一个重要特征：**每个术语都具有计算行为，并支持一种 *归约化* 概念**。原则上，归约到相同值的两个术语被称为 *定义上相等* 。它们被 Lean 的类型检查器视为"相同"，而 Lean 尽其所能识别和支持这些等同。

Lean 是一种完整的编程语言。它有一个生成二进制可执行文件和一个交互式解释器的编译器。你可以使用 `#eval` 命令执行表达式，这是测试函数的首选方法。

<!--
请注意，`#eval` 和 `#reduce` *不是*等价的。`#eval` 命令首先将 Lean 表达式编译成中间表示（IR），然后使用解释器执行生成的 IR。一些内建类型（例如`Nat`、`String`、`Array`）在 IR 中具有更高效的表示。IR 支持使用对 Lean 不透明的外部函数。
相比之下，``#reduce`` 命令依赖于与 Lean 可信核心中使用的那个相似的归约引擎，该核心负责检查和验证表达式和证明的正确性。它比 ``#eval`` 更低效，并将所有外部函数视为不透明常量。稍后您将了解这两个命令之间的其他差异。
-->

## 定义

记住，``def`` 关键字提供了一种声明新命名对象的重要方式。

```lean
def double (x : Nat) : Nat :=
  x + x
```

如果你了解其他编程语言中的函数工作方式，这样可能更容易理解：名称 `double` 被定义为接受类型为 `Nat` 的输入参数 `x` 的函数，调用的结果是 `x + x`，因此它返回类型为 `Nat`。然后，您可以使用以下方法调用此函数：

```lean
#eval double 3    -- 6
```

在这种情况下，您可以将 `def` 视为一种命名的 `lambda`，其与下面的定义方式等价：

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

当 Lean 有足够信息可以推断出类型时，您可以省略类型声明。类型推断是 Lean 的重要部分。

```lean
def double :=
  fun (x : Nat) => x + x
```

定义的一般形式是 ``def foo : α := bar``，其中 ``α`` 是从表达式 ``bar`` 返回的类型。Lean 通常可以推断出类型 ``α``，但明确写出它通常是一个好主意。这样可以明确你的意图，如果定义的右侧没有匹配的类型，Lean 会报错。

右侧的 `bar` 可以是任何表达式，不仅仅是一个 lambda。因此，`def` 也可用于简单地命名一个值，如下所示：

```lean
def pi := 3.141592654
```

`def` 可以接收多个输入参数。让我们创建一个能够将两个自然数相加的函数：

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

参数列表可以这样分隔：

```lean
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

请注意，我们在这里调用了 `double` 函数来创建 `add` 函数的第一个参数。

在 LEAN 中变量相当于零参函数，函数一般性的定义语法为

```lean
def func_name (x11 x12 ... x1n : type1) (x21 x22 ... x2n : type2) ... (xm1 xm2 ... xmn : typem) : type0 :=
  body
```

其接收类型为 `type1` 的参数 `x11, ..., x1n`，类型为 `type2` 的参数 `x21, ..., x2n`。。。，最后，返回类型为 `type0` 的值表达式 `body`。当左侧参数为空时，`func_name` 为一个常量。由于类型推断，这里很多类型声明都可以省略。


本地定义
-----------

Lean 还允许您使用 ``let`` 关键字引入“本地”定义。表达式 ``let a := t1; t2`` 在定义上等于通过将 ``t2`` 中的每个出现的 ``a`` 替换为 ``t1`` 的结果。

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

在这里，``twice_double x`` 在定义上等于 ``(x + x) * (x + x)``。

您可以通过链接 ``let`` 语句来组合多个赋值：

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

当使用换行符时，可以省略``;``。

```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

请注意，表达式 ``let a := t1; t2`` 的含义与表达式 ``(fun a => t2) t1`` 非常相似，但两者并不相同。在第一个表达式中，你应该将 ``t2`` 中的每个 ``a`` 实例视为 ``t1`` 的一种语法缩写。在第二个表达式中，``a`` 是一个变量，且 ``fun a => t2`` 表达式必须独立于 ``a`` 的值而有意义。``let`` 结构是一种更强的缩写方法，存在着 ``let a := t1; t2`` 的形式表达式，无法表示为 ``(fun a => t2) t1``。作为练习，尝试理解为什么下面的 ``foo`` 定义可以通过类型检查，但 ``bar`` 定义不能。

```lean
def foo := let a := Nat; fun x : a => x + 2
def bar := (fun a => fun x : a => x + 2) Nat
def validfunc (α β: Type) (f : α → β) (x : α) := f x
```

第一条式子，定义变量 `foo`，其取值为匿名函数 `let a := Nat; fun x : a => x + 2`。

第二条式子，表达式 `bar` 左侧 `fun a => fun x : a => x + 2` 无法通过类型检查，类似的报错写法
```lean
def bar (a : Type) := (fun x : a => x + 2) -- 返回值类型不确定
def bar (a : Type) (x : a) : Nat := x + 2 -- x 类型不确定
```

注意推敲和第三条式子的区别，表达式 `f x` 类型确定。简单说，表达式的类型应在定义后就确定，而不能依赖传入参数。

# variable 和 section

考虑以下三个函数定义:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean 提供了 ``variable`` 命令，使这样的声明看起来更简洁：

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```

也就是说，将变量提取到函数外边进行定义。你可以声明任何类型的变量，不仅仅是 ``Type`` 本身：

```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```

打印它们会发现这三组定义具有完全相同的效果。

``variable`` 命令指示 Lean 将已声明的变量按名称作为绑定变量插入到引用它们的定义中。Lean 足够聪明以确定在定义中明确或隐式使用的变量。因此，当你编写定义时，可以将 ``α``、``β``、``γ``、``g``、``f``、``h`` 和 ``x`` 视为固定对象，并让 Lean 自动为你抽象定义。注意参数逻辑是按定义顺序的，比如

```lean
variable (γ β : Type) (g : β → γ) (α : Type) (x : α)
variable (f : α → β)
def compose := g (f x)
#print compose
-- def compose : (γ β : Type) → (β → γ) → (α : Type) → (α → β) → α → γ :=
-- fun γ β g α f x => g (f x)
```

以这种方式声明的变量将在您正在使用的文件的末尾保持有效范围。然而，有时候限制变量的范围是有用的。因此，Lean提供了 ``section`` 的概念：

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

当部分关闭时，变量超出作用域，不能再被引用。

您不必对片段中的行进行缩进。您也不必为片段命名，也就是说，您可以使用一个匿名的 `section` / `end` 对。但是，如果您命名了一个片段，那么您必须使用相同的名称关闭它。片段也可以嵌套，这使您可以逐步声明新的变量。

# 命名空间

Lean 为您提供将定义分组到嵌套的分层 *命名空间* 中的功能：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

当你声明你正在使用命名空间 ``Foo`` 时，你声明的每个标识符都有一个以 ``Foo.`` 为前缀的全名。在命名空间内，你可以通过更短的名称引用标识符，但是一旦你结束了命名空间，就必须使用更长的名称。
与 ``section`` 不同，命名空间需要一个名称。在根级别只有一个匿名命名空间。

``open`` 命令将较短的名称带入当前上下文中。通常，当您导入一个模块时，您会想要打开其中一个或多个包含的命名空间，以便访问短标识符。但有时，当它们与您想要使用的另一个命名空间中的标识符发生冲突时，您可能希望将此信息保护在完全限定的名称中。因此，命名空间为您提供了在工作环境中管理名称的方法。

例如，Lean 将涉及列表的定义和定理分组到一个名为 ``List`` 的命名空间中。

```lean
#check List.nil
#check List.cons
#check List.map
```

命令 ``open List`` 允许您使用较短的名称：

```lean
open List

#check nil
#check cons
#check map
```

与章节类似，命名空间可以嵌套：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```

已关闭的命名空间可以在以后重新打开，甚至在另一个文件中：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

像章节一样，嵌套的命名空间必须按照打开的顺序闭合。命名空间和章节有不同的用途：命名空间用于组织数据，而章节用于声明插入定义的变量。章节还可用于限定诸如 `set_option` 和 `open` 之类命令的作用范围。

然而，在很多方面，``namespace ... end`` 块与 ``section ... end`` 块的行为相同。特别是，如果在命名空间中使用 ``variable`` 命令，其作用域限制于该命名空间。类似地，如果在命名空间中使用 ``open`` 命令，其效果将在命名空间关闭时消失。

## 依赖类型理论的"依赖"是什么意思？

简单解释就是，类型可以依赖于参数。你已经看到了一个很好的例子：类型 `List α` 依赖于参数 `α`，而这种依赖性正是 `List Nat` 和 `List Bool` 之间的区别所在。再举一个例子，考虑类型 `Vector α n` ，表示长度为 `n`的由 `α` 类型元素构成的向量。这个类型依赖于 *两个* 参数：向量中元素的类型(`α : Type`)以及向量的长度(`n : Nat`)。

假设你希望编写一个名为 `cons` 的函数，它可以将一个新元素插入到列表的头部。那么 `cons` 应该具有什么类型？这样的函数是 *多态的*：你期望对于 `Nat`、`Bool` 或任意类型 `α`，`cons` 函数的行为都相同。因此，将类型作为 `cons` 的第一个参数是有道理的，这样对于任何类型 `α`，`cons α` 就是类型为 `α` 的列表插入函数。换句话说，对于每个 `α`，`cons α` 是一个接受元素`a : α` 和列表 `as : List α`，并返回一个新列表的函数，因此你有 `cons α a as : List α`。

很明显，`α` 取具体值后 `cons α` 应该具有类型 `α → List α → List α`。但是 `cons` 应该具有什么类型呢？第一个猜测可能是 `Type → α → list α → list α`，但仔细思考后，这并不合理：这个表达式中的 ``α`` 并不指代任何东西，而应该指代类型 ``Type`` 的参数。`cons` 类型最左侧应是参数化的： `(α : Type) → α → list α → list α`。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

这是 *依赖函数类型* 或 *依赖箭头类型* 的一个示例。给定 ``α : Type`` 和 ``β : α → Type``，可以将 ``β`` 看作是 ``α`` 上的一组类型，即为每个 ``a : α`` 定义一个类型 ``β a``。在这种情况下，类型 ``(a : α) → β a`` 表示具有以下性质的函数 ``f`` 的类型：对于每个 ``a : α``，``f a`` 是 ``β a`` 的一个元素。换句话说，函数 ``f`` 返回的值的类型取决于其输入。

注意，对于任何表达式 ``β : Type``，表达式 ``(a : α) → β`` 都是有意义的。当 ``β`` 依赖于 ``a``（例如前一段中的表达式 ``β a``）时，``(a : α) → β`` 表示了一个依赖函数类型。而当 ``β`` 不依赖于 ``a`` 时， ``(a : α) → β`` 与类型 ``α → β`` 没有区别。实际上，在依赖类型理论（以及 Lean）中，当 ``β`` 不依赖于 ``a`` 时，``α → β`` 只是 ``(a : α) → β`` 的一种记法。

回到列表的示例，您可以使用 ``#check`` 命令来检查以下 ``List`` 函数的类型。``@`` 符号以及圆括号和花括号之间的区别将在接下来解释。

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

正如依赖函数类型 ``(a : α) → β a`` 通过允许 ``β`` 依赖于 ``α``，泛化了函数类型 ``α → β`` 的概念，依赖笛卡尔积类型 ``(a : α) × β a`` 以相同的方式泛化了笛卡尔积 ``α × β``。依赖积类型也被称为 *sigma* 类型，你也可以将它们写作 `Σ a : α, β a`。也可以使用 `⟨a, b⟩` 或 `Sigma.mk a b` 来创建一个依赖对。

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```

> 关于依赖类型，目前没有更多的细节。后续章节使用到再进一步了解。


隐式参数
------------------

假设我们有一个列表的实现，如下所示：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
```

然后，您可以按照以下方式构建 `Nat` 的列表。

```lean
#check Lst.cons Nat 0 (Lst.nil Nat) -- 空列表上添加 0

def as : Lst Nat := Lst.nil Nat -- 空列表
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat) -- 空列表上添加 5

#check Lst.append Nat as bs -- 将两个列表连接起来
```

因为构造函数在类型上是多态的，我们不得不反复插入类型 `Nat` 作为参数。但是这些信息是冗余的：可以推断出参数 `α` 是 `Lst.cons Nat 5 (Lst.nil Nat)` 这个表达式的第一个参数，因为第二个参数 `5` 的类型是 `Nat`。类似地，可以从 `Lst.cons` 函数期望在该位置有一个类型为 `Lst α` 的元素这一事实推断出 `Lst.nil Nat` 中的参数，而不是从该表达式中的其他任何信息中推断出来。

这是依赖类型理论的一个核心特点：**项携带了大量信息**，并且通常可以从上下文中推断出其中一些信息。在 Lean 中，可以使用下划线 `_` 来指定系统应该自动填充信息。这被称为“隐式参数”。

```lean
/-
  universe u
  def Lst (α : Type u) : Type u := List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil (α : Type u) : Lst α := List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
  #check Lst          -- Type u_1 → Type u_1
  #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
  #check Lst.nil      -- (α : Type u_1) → Lst α
  #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
-/
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs
```

这仍然是繁琐的，然而，要键入所有这些下划线。当函数接受一个通常可以从上下文中推断出的参数时，Lean 允许您指定该参数默认情况下应该保留为隐式。这可以通过将参数放置在花括号中来完成，如下所示：

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

所做的改变仅限于在声明变量时将 `α : Type u` 用大括号括起来。我们还可以在函数定义中使用这种语法：

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

这使得给 ``ident`` 的第一个**参数隐式**。符号上，这隐藏了类型的规格，使其看起来好像 ``ident`` 只是简单地接受任意类型的参数。事实上，标准库中的函数 ``id`` 就是以这种方式精确定义的。我们在这里选择了一个非传统的名称，只是为了避免名称冲突。

当使用 ``variable`` 命令声明变量时，变量也可以被指定为隐式的：

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

这里对 `ident` 的定义与上面的定义有相同的效果。

Lean 对于实例化隐含参数有非常复杂的机制，我们将看到**它们可以用来推断函数类型、谓词甚至证明**。将这些“洞”或“占位符”的实例化的过程通常被称为 *细化(elaboration)* 。隐含参数的存在意味着有时可能没有足够的信息来精确确定表达式的含义。像 ``id`` 或 ``List.nil`` 这样的表达式被称为 *多态*，因为它们可以在不同的上下文中具有不同的含义。

可以通过写成 ``(e : T)`` 来指定表达式 ``e`` 的类型 ``T``。这指示 Lean 的推导器在尝试解析隐含参数时使用值 ``T`` 作为 ``e`` 的类型。在下面的第二组示例中，这一机制被用来指定表达式 ``id`` 和 ``List.nil`` 的期望类型：

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

Lean 中的数字是重载的，但是当无法推断出数字的类型时，Lean 默认认为它是一个自然数。因此，下面的前两个 `#check` 命令中的表达式会以相同的方式进行解释，而第三个 `#check` 命令将 `2` 解释为一个整数。

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

有时候，我们可能会发现自己处于这样一种情况：我们声明一个函数的参数为隐式的，但现在希望明确提供该参数。如果 ``foo`` 是这样一个函数，那么符号 ``@foo`` 表示将所有隐式参数具体化的想通函数

```lean
#check @id        -- {α : Type u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

请注意，现在第一个 ``#check`` 命令将不插入任何占位符，而是显示标识符 ``id`` 的类型。此外，输出还指示第一个参数是隐含的。                                                                          