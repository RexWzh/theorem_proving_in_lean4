归纳和递归
=======================

在前一章中，我们看到归纳定义为在 Lean 中引入新类型提供了一种强大的方式。此外，构造函数和递归器是定义在这些类型上的函数的唯一方法。通过命题即类型的对应关系，这意味着归纳是证明的基本方法。

Lean 提供了自然的方式来定义递归函数，进行模式匹配，并编写归纳证明。它允许您通过指定函数应满足的方程来定义函数，它还允许您通过指定如何处理可能出现的各种情况来证明定理。在幕后，这些描述被"编译"成原始递归器，使用我们称之为"方程式编译器"的过程。方程式编译器不是可信代码库的一部分；其输出由核心独立检查的项组成。

模式匹配
----------------

模式的解释是编译过程的第一步。我们已经看到 ``casesOn`` 递归器可以根据所涉及的构造函数在归纳定义类型上定义函数和证明定理。但是，复杂的定义可能使用多个嵌套的``casesOn`` 应用，并且可能很难阅读和理解。模式匹配提供了一种更方便、更熟悉于函数式编程语言的方法。

考虑归纳定义的自然数类型。每个自然数要么是 ``zero`` ，要么是 ``succ x`` ，因此您可以通过在每种情况下指定一个值来定义从自然数到任意类型的函数：

```lean
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

这些函数的定义方程在定义上成立：

```lean
# open Nat
# def sub1 : Nat → Nat
#   | zero   => zero
#   | succ x => x
# def isZero : Nat → Bool
#   | zero   => true
#   | succ x => false
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

与 ``zero`` 和 ``succ`` 相比，我们可以使用更熟悉的符号表示：

```lean
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero : Nat → Bool
  | 0   => true
  | x+1 => false
```

因为加法和零符号被赋予了``[match_pattern]``属性，所以它们可以在模式匹配中使用。Lean会将这些表达式标准化，直到构造函数``zero``和``succ``被暴露出来。

模式匹配适用于任何归纳类型，比如乘积类型和可选类型：

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

在这里，我们不仅使用它来定义一个函数，还用它来进行分情况证明：

```lean
# namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false
# end Hidden
```

模式匹配还可以用于解构归纳定义的命题：

Given an inductive proposition, we can use pattern matching to analyze its form and extract information from it. In Coq, one way to represent inductive propositions is through the use of constructors. Each constructor represents a different case of the proposition.

For example, let's consider the natural numbers defined in Coq as an inductive proposition:

```coq
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
```

Here, `nat` is an inductive type that consists of two constructors. The `O` constructor represents zero, and the `S` constructor represents the successor of a natural number.

We can use pattern matching to analyze the form of a `nat` value. For instance, if we want to define a function `pred` that returns the predecessor of a given natural number, we can use pattern matching on the `nat` value:

```coq
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.
```

In this function, we match on the argument `n` using the `match` keyword. We have two cases: if `n` is `O`, we return `O`. If `n` is of the form `S m`, we return `m`. Through pattern matching, we are able to destructure the inductive proposition `nat` and extract the necessary information.

Pattern matching can be extended to more complex inductive propositions as well. We can define more constructors and use pattern matching to handle each possible case. This allows us to reason about and work with inductively defined propositions in a structured way.

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

这提供了一种紧凑的方式来拆分使用逻辑连接词的假设。

在所有这些例子中，模式匹配被用于进行单个案例的区分。更有趣的是，模式可以涉及嵌套构造函数，就像以下的例子中那样。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
```

方程编译器首先根据输入是否为 ``zero`` 或者 ``succ x`` 进行分割。然后它对 ``x`` 是否为 ``zero`` 或者 ``succ x`` 进行情况分割。它根据所提供的模式确定必要的情况分割，并在模式未能穷尽情况时引发错误。再次强调，我们可以使用下面的算术符号表示。无论哪种情况，这些定义方程都是定义上成立的。

```lean
# def sub2 : Nat → Nat
#   | 0   => 0
#   | 1   => 0
#   | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

你可以写``#print sub2``来查看该函数如何编译为递归函数。(Lean将告诉你``sub2``是通过一个内部辅助函数``sub2.match_1``定义的，但你也可以打印出来。) Lean使用这些辅助函数来编译``match``表达式。实际上，上面的定义被展开为：

```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x
```

下面是一些嵌套模式匹配的例子：

```lean
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

方程编译器可以按顺序处理多个参数。例如，将先前的示例定义为带有两个参数的函数会更自然：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

这里是另一个例子：

```lean
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

请注意，这些模式被逗号分隔。

在下面的示例中，拆分仅发生在第一个参数上，尽管其他参数也包含在模式列表中。

```lean
# namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
# end Hidden
```

注意，当定义中不需要参数的值时，可以使用下划线代替。这个下划线被称为 *通配模式* 或者 *匿名变量*。与方程编译器之外的使用不同，在这里下划线并不表示隐式参数。在函数式编程语言中使用下划线作为通配符是常见的，因此 Lean 采用了这种表示法。[通配符和重叠模式](#通配符和重叠模式)这一节详细介绍了通配符的概念，[不可访问模式](#不可访问模式)则解释了如何在模式中使用隐式参数。

正如在 [归纳型](./inductive_types.md) 中所述，归纳数据类型可以依赖于参数。下面的例子使用模式匹配定义了 ``tail`` 函数。参数 ``α : Type u`` 是一个参数，并且出现在冒号之前，表示它不参与模式匹配。Lean 还允许参数出现在冒号之后，但不能在它们上进行模式匹配。

```lean
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```

尽管在这两个示例中，参数 ``α`` 的位置不同，但在两种情况下它的处理方式相同，即它不参与到案例分析中。

Lean 还可以处理更复杂形式的模式匹配，其中依赖类型的参数对各种情况施加额外约束。这种 *依赖模式匹配* 的示例在 [Dependent Pattern Matching](#dependent-pattern-matching) 章节中进行了探讨。

通配符和重叠模式
----------------

考虑上一节中的一个示例：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

另一种展示方法是：

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

在第二个例子中，模式存在重叠；例如，参数对 ``0 0`` 适配了三个情况。但是 Lean 使用第一个匹配的方程来处理歧义，因此在这个例子中，最终的结果是相同的。特别地，以下等式在定义上是成立的：

```lean
# def foo : Nat → Nat → Nat
#   | 0, n => 0
#   | m, 0 => 1
#   | m, n => 2
example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl
```

因为不需要``m``和``n``的值，我们可以使用通配符模式来代替。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

您可以检查这个对 ``foo`` 的定义是否满足之前的定义特性。

一些函数式编程语言支持*不完整模式*。在这些语言中，解释器对于不完整模式可能会产生异常或返回任意值。我们可以使用 ``Inhabited`` 类型类模拟任意值的方法。粗略地说，``Inhabited α`` 类型的元素是证明了存在 ``α`` 类型元素的见证；在[类型类章节](./type_classes.md)中我们将看到，在 Lean 中可以指示适当的基本类型是有元素的，并且可以自动推断出其他构造类型也是有元素的。基于这个基础，标准库提供了任意有元素类型的默认元素 ``default``。

我们也可以使用类型 ``Option α`` 来模拟不完整模式。思路是对于已有的模式返回 ``some a``，对于不完整的情况返回 ``none``。以下示例演示了两种方法。

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

这个方程编译器非常聪明。如果你在下面的定义中漏掉了任何一种情况，错误信息将会告诉你哪些情况没有被覆盖到。

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

在适当的情况下，它还会使用“if ... then ... else”而不是 ``casesOn``。

使用``if ... then ... else``是一种在逻辑推理中常见的方式，它允许根据条件的不同结果采取不同的行动。它的一般形式是：

```
if 条件 then 操作1 else 操作2
```

其中，条件是一个布尔表达式，操作1和操作2是具体的操作或表达式。

使用``if ... then ... else``语句可以代替``casesOn``，因为它提供了一种更加简洁和灵活的方式来描述不同情况下的操作。

例如，在证明一个关于自然数的命题时，我们可以使用``if ... then ... else``来区分两种不同的情况。假设我们要证明如果一个自然数是偶数，则它可以被2整除，否则它不能被2整除。我们可以这样写：

```
Lemma even_divide_two : forall n : nat,
  (even n -> exists k : nat, n = 2 * k) /\
  (~ even n -> ~ exists k : nat, n = 2 * k).
Proof.
  intro n.
  destruct (even_dec n) as [Heven | Hnot_even].
  - (* Case: even n *)
    apply even_divide_two_helper.
    assumption.
  - (* Case: ~ even n *)
    split.
    + (* Subcase: ~ even n -> exists k : nat, n = 2 * k *)
      intros Hexists.
      contradiction Hnot_even.
      apply even_divide_two_helper.
      assumption.
    + (* Subcase: ~ even n -> ~ exists k : nat, n = 2 * k *)
      intros Hexists.
      inversion Hexists.
Qed`
```

在这个证明中，我们首先使用``destruct``来分解自然数``n``是否为偶数的假设，得到两种情况:``Heven``表示``n``是偶数，``Hnot_even``表示``n``不是偶数。然后我们使用``if ... then ... else``来处理两种情况。在第一种情况下，我们应用了一个辅助定理``even_divide_two_helper``来证明结论。而在第二种情况下，我们使用``split``将目标分为两个子目标，并使用``contradiction``和``inversion``来得到矛盾。

总之，``if ... then ... else``是一种有用的替代``casesOn``的方式，它提供了更简洁和灵活的方法来处理不同情况下的操作。

```lean
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

结构递归和归纳
----------------------------------

使得等式编译器强大的是它还支持递归定义。在接下来的三个部分中，我们将分别描述：

- 结构递归定义
- 依恋递归定义
- 互递归定义

一般来说，等式编译器处理以下形式的输入：

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

在这里 ``(a:α)`` 是一个参数序列，``(b:β)`` 是模式匹配所依赖的参数序列，``γ`` 是任意类型，可以依赖于``a``和``b``。 每一行应该包含相同数量的模式，与 ``β`` 中的元素一一对应。正如我们所看到的，模式可以是变量、构造函数应用到其他模式，或者是归一化为这种形式的表达式（非构造函数由 ``[match_pattern]`` 标记）。构造函数的出现会引发案例的分裂，构造函数的参数是指定的变量。在[Dependent Pattern Matching章节](#dependent-pattern-matching)中，我们将看到有时需要在模式中包含显式的项来使一个表达式类型检查通过，尽管它们在模式匹配中不起作用。因此，这些被称为这些是“不可访问模式”。但在[Dependent Pattern Matching章节](#dependent-pattern-matching)之前我们不需要使用这样的不可访问模式。

如我们在上一节中所见，术语 ``t₁, ..., tₙ`` 可以使用任何参数 ``a``，以及在相应模式中引入的任何变量。使递归和归纳成为可能的是它们也可以涉及对 ``foo`` 的递归调用。在本节中，我们将处理*结构递归*，即出现在“: =”右侧的 ``foo`` 的参数是左侧模式的子项。其基本思想是这些参数在结构上较小，因此在归纳类型中较早出现。以下是一些使用方程编译器定义的结构递归的示例，这些例子来自上一章节：

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n
```

``zero_add`` 的证明清楚地表明，Lean 中的归纳证明实际上是一种递归形式。

上面的例子表明，``add`` 的定义方程在定义上成立，``mul`` 也是如此。方程编译器在可能的情况下努力确保这一点，正如直接结构归纳的情况一样。然而，在其他情况下，简化只在命题上成立，也就是说，它们是必须显式应用的等式定理。方程编译器在内部生成这样的定理。用户不能直接使用它们；相反，`simp`策略被配置为在必要时使用它们。因此，`zero_add` 的以下两个证明都是有效的：

```lean
open Nat
# def add : Nat → Nat → Nat
#   | m, zero   => m
#   | m, succ n => succ (add m n)
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

与模式匹配定义一样，结构递归或归纳的参数可以出现在冒号之前。这样的参数只是在定义被处理之前添加到局部上下文中。例如，加法的定义也可以写成以下形式：

```lean
def add : nat → nat → nat
| 0     m := m,
| succ n m := succ (add n m)
```

这里，`nat` 是类型，`add` 是函数名，`: nat → nat → nat` 是函数的类型，表示接受两个 `nat` 类型的参数并返回一个 `nat` 类型的结果。

第一行是函数的定义，使用了模式匹配的方式。`| 0 m := m` 意味着当第一个参数为 `0`，第二个参数为 `m` 时，函数返回 `m`。第二行的 `succ n m` 是前面定义的自然数类型的后继构造子，表示第一个参数为 `n` 的后继。函数体 `succ (add n m)` 表示递归调用函数 `add` 并对其结果应用后继构造子。

这个定义的含义是：对于 `n` 和 `m` 两个自然数，`add n m` 表示将 `n` 和 `m` 相加的结果。如果 `n` 为 `0`，那么结果就是 `m`。否则，递归地对 `n` 的前一个自然数和 `m` 进行相加，并将结果的后继作为最终的结果。

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

你还可以使用 `match` 来编写上述示例。

```lean
def pred : nat → Prop
| zero := true
| (succ n) := false

def is_zero (n : nat) : Prop :=
match n with
| zero := true
| _ := false
end
```

在上述代码中，我们使用 `match` 来定义了两个函数 `pred` 和 `is_zero`。函数 `pred` 接受一个自然数作为参数，并返回一个命题。当参数为零时，返回真；否则返回假。函数 `is_zero` 接受一个自然数作为参数，并返回一个命题。当参数为零时，返回真；否则返回假。

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

``fib`` is defined recursively as follows:

\[
\text{{fib}}(0) = 0
\]

\[
\text{{fib}}(1) = 1
\]

\[
\text{{fib}}(n+2) = \text{{fib}}(n+1) + \text{{fib}}(n)
\]

This definition states that the Fibonacci function returns 0 for input 0, 1 for input 1, and for any other input, it returns the sum of the previous two Fibonacci numbers.

To prove that the Fibonacci function is well-defined and total, we can use structural induction.

Let's define the property \(\text{{fib\_property}}(n, x)\) as the statement: "For any \(n \geq 0\), the Fibonacci function \(\text{{fib}}\) is defined and returns \(x\) for input \(n\)."

\(\text{{fib\_property}}\) can be proven for all \(n\) using structural induction on \(n\):

**Base case:**
For \(n = 0\):
\(\text{{fib}}(0) = 0\), which matches our definition. Therefore, \(\text{{fib\_property}}(0, 0)\) holds.

For \(n = 1\):
\(\text{{fib}}(1) = 1\), which also matches our definition. Therefore, \(\text{{fib\_property}}(1, 1)\) holds.

**Inductive step:**
Assume \(\text{{fib\_property}}(k, x)\) and \(\text{{fib\_property}}(k+1, y)\) are true for some \(k \geq 1\).

We need to show that \(\text{{fib\_property}}(k+2, x+y)\) holds.

According to the definition of \(\text{{fib}}\), \(\text{{fib}}(k+2) = \text{{fib}}(k+1) + \text{{fib}}(k)\). Since \(\text{{fib\_property}}(k, x)\) and \(\text{{fib\_property}}(k+1, y)\) hold, we can substitute \(x\) and \(y\) with \(\text{{fib}}(k)\) and \(\text{{fib}}(k+1)\) respectively.

Therefore, \(\text{{fib\_property}}(k+2, x+y)\) is true.

By the principle of structural induction, \(\text{{fib\_property}}(n, x)\) holds for all \(n \geq 0\).

Thus, the Fibonacci function is well-defined and total.

In conclusion, the Fibonacci function is a more interesting example of structural recursion as it requires adding the previous two Fibonacci numbers to calculate the next one.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```

这里，``fib`` 函数在 ``n + 2``（这相当于 ``succ (succ n)``）的值被定义为在 ``n + 1``（这相当于 ``succ n``）和在 ``n`` 处的值的组合。然而，这种计算 Fibonacci 函数的方法是众所周知的低效的，其执行时间在 ``n`` 指数级增长。下面是一个更好的方法：

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

以下是使用`let rec`而不是`where`定义相同定理的代码段：

```fsharp
let rec mylt (x : nat) (y : nat) : nat =
  match x with
  | Z -> Z
  | S x1 -> add y (mylt x1 y)
```

上述代码段中的`let rec`表示这是一个递归函数的定义，而不是一个简单的函数定义。这意味着在函数体中，可以使用函数自身来进行递归调用，而不需要使用`where`子句来定义。

注意，上述代码段中的`nat`是`Lean`中的自然数类型，`Z`表示零，`S`表示后继操作，`add`表示自然数的加法操作。

带有`let rec`的代码段实现了与上一个定义相同的功能，即计算两个自然数的乘积。与以前一样，它使用模式匹配来处理自然数的可能情况，并通过递归地调用自身来实现乘法操作。

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

在这两种情况下，Lean生成辅助函数 `fibFast.loop`。

为了处理结构性递归，方程编译器使用 *course-of-values* 递归，使用自动生成的常量 ``below`` 和 ``brecOn``，这些常量与每个递归定义的类型一起使用。通过查看 ``Nat.below`` 和 ``Nat.brecOn`` 的类型，可以了解其工作原理：

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

类型 ``@Nat.below C (3 : nat)`` 是一个存储 ``C 0``、``C 1`` 和 ``C 2`` 元素的数据结构。
课程值递归可以通过 ``Nat.brecOn`` 来实现。它使我们能够根据函数的所有前一值（表示为 ``@Nat.below C n`` 的元素）来定义类型为 ``(n : Nat) → C n`` 的依赖函数在特定输入 ``n`` 处的值。

课程值递归是方程编译器用来向 Lean 内核证明函数终止性的一种技术之一。它不会影响编译递归函数的代码生成器，就像其他函数式编程语言编译器一样。记住，`#eval fib <n>` 在 `<n>` 上是指数级的。另一方面，`#reduce fib <n>` 是高效的，因为它使用基于 `brecOn` 构造的发送给内核的定义。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```

另一个很好的递归定义的例子是列表``append``函数。

``append``函数用于将两个列表拼接在一起。如果两个列表都为空，则拼接结果为空；如果第一个列表非空，则结果列表的头部是第一个列表的头部，后面跟着将第一个列表的尾部和第二个列表拼接在一起的结果。我们可以使用递归的方法来定义这个函数。

下面是用 LEAN 证明``append``函数性质的代码：

```lean
namespace append

def append {α : Type} : list α → list α → list α
| [] l := l
| (h::t) l := h :: (append t l)

notation a ++ b := append a b

theorem nil_append (l : list α) : [] ++ l = l :=
  rfl

theorem cons_append (h : α) (t l : list α) : (h :: t) ++ l = h :: (t ++ l) :=
  rfl

end append
```

我们首先定义了一个命名空间``append``，在其中定义了``append``函数。函数接受两个参数，分别是类型为``α``的两个列表。接下来，我们使用模式匹配的方式来定义``append``函数的两个情况：如果第一个列表为空，则拼接结果为第二个列表；如果第一个列表非空，我们将第一个列表的头部``h``与将第一个列表的尾部``t``与第二个列表``l``拼接的结果组成一个新的列表。

``append``函数还定义了一个可读性更好的符号``++``来表示列表的拼接运算。

在上面给出的代码中，我们还给出了两个定理的证明来验证``append``函数的性质。首先，``nil_append``定理说明了如果将一个空列表``[]``与另一个列表``l``拼接，结果应该是``l``本身。其次，``cons_append``定理说明了如果将一个非空列表``(h :: t)``与另一个列表``l``拼接，结果应该是将``h``添加到``t``与``l``拼接的结果的头部。这两个定理的证明使用了先前定义的``append``函数的模式匹配规则。

通过这种递归的方式定义``append``函数，我们可以方便地进行列表的拼接操作，并且保持代码的简洁性和可读性。

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

这里有另一个函数:它将第一个列表的元素与第二个列表的元素相加，直到两个列表中的一个用尽为止。

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

你可以使用 `let rec` 关键字定义本地递归声明。

```lean
def factorial : ℕ → ℕ
| 0 := 1
| (n+1) := (n+1) * factorial n

#eval factorial 5
```
在这个例子中，我们定义了一个阶乘函数 `factorial`，它接受一个自然数作为输入，并返回其阶乘的结果。在函数体内部，我们使用了模式匹配的方式来处理不同的情况。如果输入为 `0`，那么阶乘的结果就是 `1`；如果输入为 `n+1`（其中 `n` 是大于等于 `0` 的自然数），那么阶乘的结果就是 `(n+1) * factorial n`，即 `(n+1)` 乘以 `n` 的阶乘。最后，我们通过调用 `factorial 5` 来计算 `5` 的阶乘，并使用 `#eval` 指令将其输出。

希望你能通过练习来尝试类似的例子。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

Lean 对于每个 `let rec` 创建了一个辅助声明。在上面的例子中，它为出现在 `replicate` 处的 `let rec loop` 创建了声明 `replicate.loop`。请注意，Lean 通过将 `let rec` 声明中出现的局部变量添加为额外参数来 "关闭" 声明。例如，在 `let rec loop` 中出现的局部变量 `a`。

你也可以在策略模式下使用 `let rec` 来创建归纳证明的证明。

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

你还可以在你的定义之后使用 `where` 子句引入辅助递归声明。
Lean 将它们转换为 `let rec`。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

基于良基递归和归纳
------------------------------------

当结构递归无法使用时，我们可以使用良基递归来证明终止性。我们需要一个良基关系，并证明每个递归应用对于这个关系来说是递减的。依赖类型理论足够强大，可以对良基递归进行编码和证明。让我们从逻辑背景开始，以便理解其工作原理。

Lean标准库定义了两个谓词，``Acc r a`` 和 ``WellFounded r``，其中 ``r`` 是类型``α``上的二元关系，而 ``a`` 是类型 ``α`` 的一个元素。

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

第一个谓词 "Acc" 是一个归纳定义的谓词。根据它的定义，"Acc r x" 等价于 "∀ y, r y x → Acc r y"。如果我们将 "r y x" 看作一种顺序关系 "y ≺ x"，那么 "Acc r x" 表示 "x" 从下方可达，也就是说它的所有前驱都是可达的。特别地，如果 "x" 没有任何前驱，那么它是可达的。对于任意类型 "α"，我们应该能够通过首先给所有前驱赋值来递归地为 "α" 中的每个可达元素赋值。

谓词 "r" 是"良基"（well founded）的表述，记作 "WellFounded r"，实际上是类型中的每个元素都是可达的表述。以上考虑表明，如果 "r" 是作用在类型 "α" 上的一个良基关系，那么我们应该拥有一个相对于关系 "r" 在类型 "α" 上进行良基递归运算的原则。实际上，我们确实拥有：标准库定义了函数 "WellFounded.fix"，正好用于这个目的。

```lean
noncomputable def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F
```

这里有一系列的角色，但第一个块我们已经见过了：类型 ``α``，关系 ``r``，以及假设 ``h``，即 ``r`` 是良基的。变量 ``C`` 表示递归定义的目的：对于每个元素 ``x:α``，我们想要构造一个 ``C x`` 的元素。函数 ``F`` 提供了构造元素 ``C x`` 的归纳步骤：它告诉我们如何在给定每个前身 ``y`` 的 ``C y`` 的元素的情况下构造 ``C x`` 的元素。

请注意，``WellFounded.fix`` 同样适用于归纳原则。它表示如果 ``≺`` 是良基的并且你想要证明 ``∀x, C x``，只需要证明对于任意的 ``x``，如果我们有 ``∀y ≺ x, C y``，那么我们就有 ``C x``。

在上面的示例中，我们使用了 `noncomputable` 修饰词，因为代码生成器当前不支持 `WellFounded.fix`。函数 `WellFounded.fix` 是 Lean 用来证明函数终止的另一个工具。

Lean 知道自然数上的通常顺序 ``<`` 是良基的。它还知道许多从其他基础顺序构建新良基顺序的方法，例如使用字典顺序。

下面是在标准库中找到的自然数除法的基本定义。

```lean
open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

这个定义有些晦涩。这里的递归是在“x”上进行的，而“div.F x f: Nat → Nat”返回了针对固定“x”的“除以y”函数。您必须记住，“div.F”的第二个参数，即递归的配方，是一个函数，它应该返回所有小于“x”的值“x₁”的“除以y”函数。

这个推导器是为了使这样的定义更加方便而设计的。它接受以下内容：

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0
```

当 Lean 遇到递归定义时，首先尝试结构递归，只有在失败时才会退回到良基递归。Lean 使用 `decreasing_tactic` 策略来展示递归应用较小。上面例子中的辅助命题 `x - y < x` 应被视为该策略的提示。

`div` 的定义方程 *不* 是严格成立的，但我们可以使用 `unfold` 策略来展开 `div`。我们使用 [`conv`](./conv.md) 来选择要展开的 `div` 应用。

```lean
# def div (x y : Nat) : Nat :=
#  if h : 0 < y ∧ y ≤ x then
#    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
#    div (x - y) y + 1
#  else
#    0
example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div -- unfold occurrence in the left-hand-side of the equation

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

下面的例子与之类似：它将任何自然数转换为以0和1表示的二进制表达式，表示为一个列表。我们需要提供递归调用是递减的证据，我们在这里使用``sorry``来说明。``sorry``并不会阻止解释器成功执行函数。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval natToBin 1234567
```

作为最后一个示例，我们观察到 Ackermann 函数可以直接定义，因为它是通过自然数上的字典序的良定义性来证明的。`termination_by` 子句指示 Lean 使用一个字典序。此子句实际上是将函数参数映射到类型为 `Nat × Nat` 的元素上。然后，Lean 使用类型类解析来合成一个类型为 `WellFoundedRelation (Nat × Nat)` 的元素。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)
```

请注意，上面的例子中使用了字典序，因为 `WellFoundedRelation (α × β)` 实例使用了字典序。Lean 还定义了该实例。

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```

在下面的例子中，我们通过展示递归应用中 `as.size - i` 正在减小来证明终止性。

```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
termination_by go i r => as.size - i
```

请注意，此示例中的辅助函数 `go` 是递归的，但 `takeWhile` 不是。

默认情况下，Lean 使用 `decreasing_tactic` 策略来证明递归应用是递减的。修饰符 `decreasing_by` 允许我们使用自己的策略。以下是一个示例。

```
def takeWhile {α : Type} (p : α → Prop) : list α → list α :=
  fix go : list α → list α :=
    λ xs, match xs with
          | []         := []
          | (x :: xs') := if p x then x :: go xs' else []
          end
  in go
```

在这个例子中，`takeWhile` 函数的定义包含一个名为 `go` 的辅助函数。这个辅助函数使用`fix`来定义，这意味着它是递归的。通过模式匹配，`go` 在遇到空列表时返回空列表，否则会检查列表中的第一个元素是否满足谓词 `p`。如果满足，则将第一个元素加入结果列表，并递归调用 `go` 处理剩下的元素。如果不满足，直接返回空列表。

需要注意的是，`go` 在递归调用时可能会引发警告，因为默认情况下 Lean 会使用 `decreasing_tactic` 来确保递归调用是递减的。如果使用者没有提供递减证明，Lean 可能会报出“应用了非递减参数”的错误。使用 `decreasing_by` 修饰符可以允许我们自定义递减证明的策略。

点击[此处](https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html#recursor-decreasing)了解更多关于自定义递减证明策略的内容。

```lean
theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption
```

注意，`decreasing_by`不是`termination_by`的替代品，它们是互补的。`termination_by`用于指定一个良序关系，而`decreasing_by`用于提供我们自己的策略来证明递归应用是递减的。在下面的示例中，我们都使用了它们。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)
decreasing_by
  simp_wf -- unfolds well-founded recursion auxiliary definitions
  first | apply Prod.Lex.right; simp_arith
        | apply Prod.Lex.left; simp_arith
```

我们可以使用 `decreasing_by sorry` 来告诉 Lean "相信" 我们的函数会终止。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval natToBin 1234567
```

回想一下，使用 `sorry` 和使用一个新公理是等价的，应该避免使用。在下面的例子中，我们使用了 `sorry` 来证明 `False`。命令 `#print axioms` 显示出 `unsound` 依赖于不完备公理 `sorryAx`，而该公理用于实现 `sorry`。

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound
-- 'unsound' depends on axioms: [sorryAx]
```

互递归
----------------

Lean 也支持互递归的定义。其语法与互归归纳类型相似。下面是一个例子：

```lean
mutual def even, odd : Nat → Prop
| 0     => true
| (n+1) => odd n
with odd : Nat → Prop
| 0     => false
| (n+1) => even n
```

在上面的例子中，`even` 和 `odd` 是两个互递归的函数，它们递归地定义了自然数是否为偶数和奇数的性质。

证明
----
为了证明递归函数的终止性，Lean 提供了 `termination_by` 类来指定使用哪个类型的良序关系。如果没有指定 `termination_by`，Lean 将根据函数参数的类型使用类型类解析来推导良序关系。

如果指定了 `termination_by`，它将函数的参数映射到类型 `α` 上，并且再次使用类型类解析。需要注意的是，默认情况下，`β × γ` 的默认实例是基于 `β` 和 `γ` 的良序关系构建的词典序。

对于自然数 `Nat`，默认的良序关系实例是 `<` 关系。

默认情况下，`decreasing_tactic` 策略用于证明递归应用相对于选择的良序关系来说更小。如果 `decreasing_tactic` 失败，错误信息中将包含剩余的目标 `... |- G`。需要注意的是，`decreasing_tactic` 使用 `assumption` 策略。因此，您可以使用 `have` 表达式来证明目标 `G`。您还可以使用 `decreasing_by` 来提供自己的策略。

```lean
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]
```

这是一个互相定义的特点在于，``even``是在``odd``的基础上进行递归定义，而``odd``又是在``even``的基础上进行递归定义。在底层，这被编译为一个单一的递归定义。内部定义的函数接受一个和类型的元素作为参数，可以是``even``的输入，也可以是``odd``的输入。然后返回与输入相适应的输出。为了定义这个函数，Lean使用了一个合适的良序测度。内部细节应该对用户隐藏起来；使用这样的定义的正统方式是使用``simp``（或者``unfold``），就像我们之前所做的那样。

互相递归定义也提供了处理互相嵌套归纳类型的自然方式。回想一下之前介绍的``Even``和``Odd``作为互相归纳谓词的定义。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end
```

构造函数 ``even_zero``、``even_succ`` 和 ``odd_succ`` 提供了判断一个数是偶数还是奇数的正面手段。为了知道零不是奇数，并且后两个蕴含式是相反的，我们需要使用归纳类型是由这些构造函数生成的这个事实。通常情况下，构造函数被保存在一个以定义类型命名的命名空间中，``open Even Odd`` 命令允许我们更方便地访问它们。

```lean
# mutual
#  inductive Even : Nat → Prop where
#    | even_zero : Even 0
#    | even_succ : ∀ n, Odd n → Even (n + 1)
#  inductive Odd : Nat → Prop where
#    | odd_succ : ∀ n, Even n → Odd (n + 1)
# end
open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h
```

再举一个例子，假设我们使用嵌套的归纳类型来递归地定义一组术语。在这个定义中，一个术语要么是一个常量（由一个字符串表示的名称），要么是将一个常量应用于一组常量的结果。

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

然后我们可以使用互递归定义来统计项中出现的常数数量，以及项列表中出现的常数数量。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]

#eval numConsts sample

end Term
```

作为最后一个例子，我们定义一个函数`replaceConst a b e`，它在表达式`e`中将常量`a`替换为`b`，然后证明常量的数量保持不变。注意，我们的证明使用了互递归（也称为归纳法）。

```lean
theorem replace_const_preserves_no_consts : ∀ a b : expr, ∀ e : expr, no_consts (replace_const a b e) = no_consts e :=
begin
  /- proof by mutual recursion -/

  -- base case: `e` is a variable
  intros a b e,
  cases e,
  simp [replace_const],

  -- inductive case 1: `e` is `const a`
  intros a b e,
  cases e,
  simp [replace_const, no_consts],

  -- inductive case 2: `e` is `app e₁ e₂`
  intros a b e,
  cases e,
  simp [replace_const, no_consts],
  rw [replace_const_preserves_no_consts, replace_const_preserves_no_consts],
end
```

这个定理证明了在一个表达式`e`中，用常量`a`替换为`b`后，常量的数量保持不变。证明使用了互递归的方法，通过分析表达式`e`的各种情况来进行证明。最后的两个归纳步骤使用了递归调用来证明替换后常量的数量仍然保持不变。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
# namespace Term
# mutual
#  def numConsts : Term → Nat
#    | const _ => 1
#    | app _ cs => numConstsLst cs
#   def numConstsLst : List Term → Nat
#    | [] => 0
#    | c :: cs => numConsts c + numConstsLst cs
# end
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
            : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
            : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
```

依赖模式匹配
--------------------------

我们在 [模式匹配章节](#pattern-matching) 中讨论的所有模式匹配例子都可以很容易地使用 ``cases_on`` 和 ``rec_on`` 写出来。但是，对于索引的归纳族，比如 ``Vector α n``，情况通常并非如此，因为情况分割之后对索引的值施加了一些约束。如果没有等式编译器，我们将需要大量样板代码来用递归函数定义非常简单的函数，比如 ``map``，``zip`` 和 ``unzip``。为了理解其中的困难，考虑一下定义一个函数 ``tail``，它取一个向量 ``v : Vector α (succ n)`` 并删除第一个元素。最初的想法可能是使用 ``casesOn`` 函数：

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector
```

但是在“nil”情况下应该返回什么值呢？有一件有趣的事情发生了：如果 ``v`` 的类型是 ``Vector α (succ n)``，它*不可能*是空的，但是如何告诉 ``casesOn`` 这一点并不清楚。

一种解决方法是定义一个辅助函数：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
# end Vector
```

在 ``nil`` 的情况下，``m`` 被实例化为 ``0``，``noConfusion`` 利用了 ``0 = succ n`` 不能出现的事实。否则，``v`` 的形式是 ``a :: w``，我们可以将它从长度为 ``m`` 的向量转换为长度为 ``n`` 的向量后简单地返回 ``w``。

定义 ``tail`` 的难点在于保持索引之间的关系。``tailAux`` 中的假设 ``e : m = n + 1`` 被用来传递 ``n`` 和与次前提相关联的索引之间的关系。此外，``zero = n + 1`` 的情况是不可到达的，而丢弃这样的情况的规范方式是使用 ``noConfusion``。

然而，使用递归方程很容易定义 ``tail`` 函数，方程编译器会自动生成所有样板代码。以下是一些类似的例子：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

请注意，我们可以省略“无法到达（unreachable）”情况下的递归方程，例如 ``head nil``。对于索引族的自动生成定义远非简单。例如：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

#print map
#print map.match_1
# end Vector
```

用手动定义``map``函数比定义``tail``函数更烦琐。我们鼓励你使用``recOn``、``casesOn``和``noConfusion``来尝试定义它。

不可访问的模式
------------------

有时，一个依赖匹配模式中的参数在定义中并不重要，但是仍然必须包含它以适当地特化表达式的类型。Lean允许用户将这种子项标记为对模式匹配不可访问的。这些注释在左侧出现的项既不是变量也不是构造应用的情况下是必不可少的，因为它们不能作为模式匹配的目标。我们可以将这样的不可访问模式视为模式的“不关心”组成部分。你可以通过写``.(t)``来声明一个子项不可访问。如果可以推断出不可访问模式，你也可以写``_``。

在下面的示例中，我们声明了一个归纳类型，它定义了“在``f``的图像中”的属性。你可以将类型``ImageOf f b``的元素视为``b``在``f``的图像中的证据，其中构造函数``imf``用于构建这样的证据。然后，我们可以定义任何具有“反函数”的函数``f``，该函数接受``f``的图像中的任何元素，并将其映射到它所映射的元素。类型规则强制我们为第一个参数写``f a``，但是这个表达式既不是变量也不是构造应用，并且在模式匹配定义中不起任何作用。为了定义下面的函数``inverse``，我们*必须*将``f a``标记为不可访问的。

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

在上面的例子中，不可访问的注解明确表示``f``不是一个模式匹配变量。

不可访问的模式可以用于澄清和控制使用依赖模式匹配的定义。考虑下面的函数``Vector.add``的定义，该函数用于将两个元素类型为类型的向量相加，假设该类型有一个相关的加法函数：

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

end Vector
```

在冒号之后出现的 ``{n : Nat}`` 是因为它不能在整个定义过程中保持不变。在实现这个定义时，方程编译器会首先根据第一个参数是 ``0`` 还是 ``n+1`` 进行情况区分。然后会在下面的两个参数上进行嵌套的情况分割，在每种情况下，方程编译器会排除与第一个模式不兼容的情况。

然而，事实上，我们并不需要在第一个参数上进行情况分割；``Vector`` 的 ``casesOn`` 消除器会自动抽象该参数并在对第二个参数进行情况分割时用 ``0`` 和 ``n+1`` 替换它。使用不可访问模式，我们可以提示方程编译器避免在 ``n`` 上进行情况分割。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

将位置标记为不可访问模式告诉等式编译器第一，要从其他参数的约束来推断该参数的形式，第二，第一个参数不应参与模式匹配。

不可访问模式 `.(_)` 可以简写为 `_`。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

正如我们上面提到的，参数 ``{n : Nat}`` 是模式匹配的一部分，因为它不能在整个定义过程中保持固定。在以前的 Lean 版本中，用户经常发现必须包含这些额外的判别式很麻烦。因此，Lean 4 实现了一个新特性，*判别式的细化*，它会自动为我们包含这些额外的判别式。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

当与 *auto bound implicits* 功能结合使用时，您可以进一步简化声明并写入：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

使用这些新特性，您可以更紧凑地编写之前部分中定义的其他向量函数，如下所示：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

匹配表达式
----------

LEAN 还提供了一个编译器，用于处理许多函数式语言中的 *match-with* 表达式。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

这看起来与普通的模式匹配定义并没有太大的区别，但关键点在于``match``语法可以在表达式的任何位置使用，并且可以接受任意参数。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

下面是另一个例子：

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

Lean 在系统的所有部分内部使用 ``match \ldots with`` 结构来实现模式匹配。因此，这四个定义具有相同的最终效果。

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

这些变体同样适用于解读命题：

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```

使用 `let rec` 关键字可以定义局部递归声明。

```ocaml
let rec factorial n =
  if n <= 1 then
    1
  else
    n * factorial (n - 1)
```

在上面的示例中，`factorial` 函数是一个局部递归函数。它以一个整数 `n` 作为参数，并返回 `n` 的阶乘。函数内部首先检查 `n` 是否小于等于 1，如果是，则返回 1。否则，它递归地调用自身，并将 `n` 减去 1 作为参数。递归调用的结果与 `n` 相乘，得到最终的阶乘结果。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

Lean为每个`let rec`创建了一个辅助声明。在上面的例子中，它为出现在`replicate`的`let rec loop`创建了声明`replicate.loop`。注意，Lean通过将出现在`let rec`声明中的任何局部变量添加为额外的参数来"关闭"声明。例如，局部变量`a`出现在`let rec loop`中。

在策略模式下，您也可以使用`let rec`来创建归纳证明。

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

你还可以在定义后使用 `where` 子句引入辅助递归声明，Lean 会将其转换为 `let rec`。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

练习
---------
1. 打开命名空间``Hidden``以避免命名冲突，并使用等式编译器定义自然数上的加法、乘法和指数运算。然后使用等式编译器推导出它们的一些基本属性。

2. 类似地，使用等式编译器定义列表的一些基本操作（如``reverse``函数），并通过归纳证明关于列表的定理（例如对于任意列表``xs``，有``reverse (reverse xs) = xs``）。

3. 定义自己的函数来对自然数进行值域递归。类似地，看看自己能否弄清楚如何定义``WellFounded.fix``。

4. 按照[依赖模式匹配章节](#dependent-pattern-matching)中的示例，定义一个函数来追加两个向量。这有点棘手，你将不得不定义一个辅助函数。

5. 考虑以下类型的算术表达式。理念是``var n``是一个变量``vₙ``，``const n``是值为``n``的常量。

```lean
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
```

在这里，“sampleExpr”代表“(v₀ * 7) + (2 * v₁)”。

编写一个函数来求解这样的表达式，将每个“var n”求值为“v n”。

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr
```

实现"常数融合"（constant fusion）的过程，该过程将简化如 ``5 + 7`` 这样的子项为 ``12``。使用辅助函数 ``simpConst``，定义一个名为 "fuse" 的函数：对于加法或乘法表达式，先递归地简化参数，然后应用 ``simpConst`` 尝试简化结果。

```lean
-- 定义常数融合辅助函数 simpConst
def simpConst : expr → option ℕ
| `(nat.zero) := some 0
| `(nat.succ %%n) := some $ 1 + simpConst n
| _ := none

-- 定义常数融合函数 fuse
def fuse : expr → option expr
| `(%%x + %%y) := match (fuse x, fuse y) with
                  | (some x', some y') := match simpConst `(%%x' + %%y') with
                                         | some c := some `(nat.num %%c)
                                         | none := some `(%%x' + %%y')
                                         end
                  | _ := none
                  end
| `(%%x * %%y) := match (fuse x, fuse y) with
                  | (some x', some y') := match simpConst `(%%x' * %%y') with
                                         | some c := some `(nat.num %%c)
                                         | none := some `(%%x' * %%y')
                                         end
                  | _ := none
                  end
| _ := none
```

此代码是基于 Lean 证明助手编写的，用于对简单的加法和乘法表达式进行常数融合。首先，我们定义了一个辅助函数 `simpConst`，通过模式匹配来简化给定的表达式。它会尝试将表达式转换为数字常量（即 `nat.num`）。

然后，我们定义了一个函数 `fuse`，它使用模式匹配来搜索加法和乘法表达式，并递归地简化它们的参数。然后，它应用 `simpConst` 辅助函数来尝试简化结果。如果结果是一个数字常量，那么它将返回相应的 `nat.num` 表达式。否则，它会返回简化的加法或乘法表达式。

请注意，这只是一个简单的示例，实际应用中的常数融合可能更复杂，并可能需要更复杂的处理逻辑。我们只是展示了一种基本的实现方式。

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def eval (v : Nat → Nat) : Expr → Nat
#   | const n     => sorry
#   | var n       => v n
#   | plus e₁ e₂  => sorry
#   | times e₁ e₂ => sorry
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
```

最后两个定理证明了这些定义保持值的不变。