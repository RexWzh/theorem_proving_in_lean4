策略模式
=========

在一个策略块中，你可以使用关键字 `conv` 进入转换模式。在这个模式下，可以在假设和目标中导航，甚至在函数抽象和依赖箭头中，应用重写或简化步骤。

基本导航和重写
-----------

首先，让我们证明一个例子 `(a b c : Nat) : a * (b * c) = a * (c * b)` （本文件中的例子有些不切实际，因为其他策略可以立即完成它们）。最初的尝试是进入策略模式并尝试 `rw [Nat.mul_comm]`。但这会把目标转化为 `b * c * a = a * (c * b)`，在这个术语中，第一个出现的乘法被交换了。有几种修复这个问题的方法，其中一种方法是使用一个更精确的工具：转换模式。下面的代码块显示了每行执行后的当前目标。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    congr
    -- 2 goals: ⊢ a, ⊢ b * c
    rfl
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

上面的片段显示了三个导航命令：

- `lhs`导航到关系的左侧（在这里是等式），还有一个`rhs`导航到右侧。
- `congr`根据当前头函数（这里是乘法）的（非依赖的和显式的）参数创建相同数量的目标。
- `rfl`使用自反性来关闭目标。

一旦到达相关的目标，我们可以像正常策略模式一样使用`rw`命令。

使用转换模式的第二个主要原因是在限定词下进行重写。假设我们想要证明示例`(fun x : Nat => 0 + x) = (fun x => x)`。最初的尝试是进入策略模式并尝试`rw [Nat.zero_add]`。但这将导致令人沮丧的失败。

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

解决方案是：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

其中 `intro x` 是进入 `fun` 文件夹的导航命令。
需要注意的是这个示例有些人为，也可以这样做：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

或者只是

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

`conv` 还可以使用 `conv at h` 从本地环境中重写一个假设 `h`。

模式匹配
-------

使用上述命令进行导航可能会很繁琐。我们可以使用模式匹配来简化操作，如下所示：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
```

这只是一种语法糖，即为

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

当然，通配符是允许的：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

结构化转化策略
-------

花括号和点号也可用于`conv`模式，以结构化转化策略。

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

转化模式中的其他策略
----------

- `arg i` 输入应用程序的第`i`个非依赖显式参数。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    arg 2
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

- `args` 是 `congr` 的另一个名称。

- `simp` 将简化器应用于当前目标。它支持在常规策略模式下可用的相同选项。

```lean
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁
```

- 使用给定的参数迭代`arg`和`intro`，输入为`[1, x, 2, y]`。这只是一个宏：

```
syntax enterArg := ident <|> group("@"? num)
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i:num]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))
```

- `done` 如果存在未解决的目标，则失败。

- `trace_state` 显示当前策略的状态。

- `whnf` 将术语转换为弱头正常形式。

- `tactic => <tactic sequence>` 返回常规策略模式。这对于不受 `conv` 模式支持的目标的消除以及应用自定义的合同和外延引理非常有用。

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- ⊢ g x x + x
    arg 1
    -- ⊢ g x x
    rw [h₁]
    -- 2 goals: ⊢ 1, ⊢ x ≠ 0
    . skip
    . tactic => exact h₂
```

- `<term>` 的应用是 `tactic => apply <term>` 的语法糖

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
```

