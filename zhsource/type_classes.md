# 类型类

类型类被引入为函数式编程语言中实现特殊多态的一种有原则的方式。首先我们观察到，如果函数仅仅以类型特定的加法实现作为参数，然后在剩余的参数上调用该实现，实现一个特殊的多态函数（比如加法）将变得很容易。例如，假设我们在 Lean 中声明一个结构来保存加法的实现。

```lean
# namespace Ex
structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
# end Ex
```

在上面的 Lean 代码中，`add` 字段的类型为 `Add.add : {a : Type} → Add a → a → a → a`，其中大括号表示 `a` 是一个隐含参数。
我们可以这样实现 `double` 函数：

```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a → a → a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20
# end Ex
```

请注意，你可以通过 `double { add := Nat.add } n` 将一个自然数 `n` 乘以2。
当然，如果用户手动传递实现，将会非常麻烦。
实际上，这样做会削弱ad-hoc多态的潜在收益。

类型类的主要思想是将诸如 `Add a` 的参数隐藏起来，并使用用户定义的实例数据库通过一个称为类型类解析的过程自动合成所需的实例。
在 Lean 中，通过将上面示例中的 `structure` 改为 `class`，`Add.add` 的类型变为：

```lean
# namespace Ex
class Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```

其中方括号表示类型为 `Add a` 的参数是*隐式实例*，即应使用类型类解析来综合生成。这个版本的 `add` 是 Lean 中对应 Haskell 术语 `add :: Add a => a -> a -> a` 的模拟。类似地，我们可以通过下面的方式注册实例：

```lean
# namespace Ex
# class Add (a : Type) where
#  add : a → a → a
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
# end Ex
```

那么对于 `n : Nat` 和 `m : Nat`，术语 `Add.add n m` 触发类型类解析，目标是 `Add Nat`，并且类型类解析将合成上述 `Nat` 的实例。我们现在可以使用隐式实例来重新实现 `double`，方法是：

```lean
# namespace Ex
# class Add (a : Type) where
#   add : a → a → a
# instance : Add Nat where
#  add := Nat.add
# instance : Add Int where
#  add := Int.add
# instance : Add Float where
#  add := Float.add
def double [Add a] (x : a) : a :=
  Add.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

#eval double 10
-- 20

#eval double (10 : Int)
-- 100

#eval double (7 : Float)
-- 14.000000

#eval double (239.0 + 2)
-- 482.000000

# end Ex
```

一般来说，实例之间可能以复杂的方式相互依赖。例如，您可以声明一个（匿名）实例，即如果 `a` 具有加法，则 `Array a` 具有加法功能：

```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (· + ·)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```

注意，在 Lean 中 `(· + ·)` 是 `fun x y => x + y` 的一种表示方式。

上面的示例展示了如何使用类型类进行记法的重载。
现在，我们来探讨另一个应用场景。我们经常需要一个给定类型的任意元素。
在 Lean 中，类型可能没有任何元素。
通常情况下，我们希望在某些“边角情况”下，定义能够返回一个任意元素。
例如，当 `xs` 的类型是 `List a` 时，我们希望表达式 ``head xs`` 的类型为 ``a``。
类似地，许多定理在额外假设类型非空的情况下成立。
例如，如果 `a` 是一个类型，那么 ``exists x : a, x = x`` 只有在 `a` 非空时才为真。
标准库定义了一个类型类 ``Inhabited``，使得类型类推断能够推断出一个非空类型的“默认”元素。
让我们从上面程序的第一步开始，声明一个适当的类：

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```

注意 `Inhabited.default` 没有任何显式的参数。

``Inhabited a`` 类的元素简单地表示为形如 ``Inhabited.mk x`` 的表达式，其中 ``x: a`` 是某个元素。
投射函数 ``Inhabited.default`` 将允许我们从 ``Inhabited a`` 的元素中“提取”出 ``a`` 的元素。
现在我们为该类提供一些实例：

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```

你可以使用命令 `export` 为 `Inhabited.default` 创建别名 `default`。

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```

## 嵌套实例化

如果这就是类型类推断的全部内容，那就不是很令人印象深刻；
这只是一种将实例存储在查找表中以供推导器查找的机制。
使类型类推断强大的是它可以*嵌套*实例化。也就是说，
一个实例声明可以依赖于类型类的一个隐式实例。
这会导致类推断通过递归地链式实例化，并在需要时进行回溯，类似于 Prolog 中的搜索。

例如，下面的定义表明，如果两个类型``a``和``b``是可行的，那么它们的乘积也是可行的：

```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```

在之前的实例声明中添加了这个之后，类型类实例可以推导出，例如，``Nat × Bool`` 的默认元素：

```haskell
instance (Default a, Default b) => Default (a, b) where
  def = (def, def)
```

这个实例声明表示，当类型 ``a`` 和 ``b`` 都有默认实现时，``(a, b)`` 类型的默认实现就是 ``(def, def)``。这样，通过这个实例声明，我们可以为 ``Nat × Bool`` 类型推导出一个默认元素。

在这个例子中，如果 ``Nat`` 和 ``Bool`` 类型都有定义了 ``Default`` 类型类的实例，那么 ``(def, def)`` 就会成为 ``Nat × Bool`` 的默认元素。

对于其他的类型，我们可以根据具体的需求提供不同的实现。通过定义实例，我们可以满足不同类型的默认值需求。在本例中，我们定义了一个通用的实例，可以适用于所有具有 ``Default`` 实例的类型对 ``(a, b)``。

```lean
# namespace Ex
# class Inhabited (a : Type u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# opaque default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```

类似地，我们可以用适当的常量函数填充类型函数：

```lean
instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default
```

作为一个练习，尝试为其他类型（如 `List` 和 `Sum` 类型）定义默认实例。

Lean 标准库中包含了 `inferInstance` 的定义。它的类型是 `{α : Sort u} → [i : α] → α`，在期望类型是一个实例时触发类型类解析过程非常有用。

```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```

您可以使用 `#print` 命令来检查 `inferInstance` 函数的简单性。

```lean
#print inferInstance
```

## ToString

多态方法 `toString` 的类型为 `{α : Type u} → [ToString α] → α → String`。您可以为自己的类型实现该实例，并使用链式调用将复杂的值转换为字符串。Lean已经为大多数内置类型提供了 `ToString` 实例。

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
```

## 数字

数字在 Lean 中是多态的。你可以使用一个数字（例如 `2`）来表示任何实现了类型类 `OfNat` 的类型的元素。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat
```

在 Lean 中，`(2 : Nat)` 和 `(2 : Rational)` 这两个术语的展开形式分别为 `OfNat.ofNat Nat 2 (instOfNatNat 2)` 和 `OfNat.ofNat Rational 2 (instOfNatRational 2)`。我们称展开形式中出现的数字 `2` 为原始自然数。你可以使用宏 `nat_lit 2` 来表示原始自然数 `2`。

```lean
#check nat_lit 2  -- Nat
```

原始自然数 *不是* 多态的。

`OfNat` 类型类是通过数字参数化的。因此，您可以为特定数字定义实例。
第二个参数通常是一个变量，就像上面的示例一样，或者是一个 *原始* 自然数。

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

## 输出参数

默认情况下，当项 `T` 已知且不包含缺失部分时，Lean 仅尝试合成实例 `Inhabited T`。下面的命令会产生错误"类型类实例问题被卡住，常常是由于元变量 `?m.7`"，因为类型中有一个缺失部分（即 `_`）。

```lean
#check_failure (inferInstance : Inhabited (Nat × _))
```

你可以将类型类 `Inhabited` 的参数视为类型类合成器的*输入*值。当一个类型类有多个参数时，你可以将其中一些标记为输出参数。即使这些参数有缺失的部分，Lean也会启动类型类合成器。在下面的示例中，我们使用输出参数来定义一个*异构*多态乘法。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```

参数 `α` 和 `β` 被认为是输入参数，而 `γ` 是一个输出参数。
给定一个应用程序 `hMul a b`，在知道 `a` 和 `b` 的类型之后，类型类综合器会被调用，并从输出参数 `γ` 中获取到结果类型。
在上面的例子中，我们定义了两个实例。第一个实例是自然数的同类乘法。第二个实例是数组的标量乘法。
注意，您可以将实例链接起来并泛化第二个实例。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
# end Ex
```

当你拥有一个实例 `HMul α β γ` 时，你可以在 `Array β` 类型的数组上使用我们的新的标量数组乘法实例，标量的类型是 `α`。在最后的 `#eval` 中，注意实例在一个数组的数组上被使用了两次。

## 默认实例

在类 `HMul` 中，参数 `α` 和 `β` 被视为输入值。因此，类型类合成仅在这两个类型已知之后才开始。这可能经常过于限制。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
#check_failure fun y => xs.map (fun x => hMul x y)
# end Ex
```

实例 `HMul` 没有被 Lean 合成，因为没有指定 `y` 的类型。
然而，在这种情况下，默认情况下我们可以假设 `y` 和 `x` 的类型应该相同。我们可以使用*默认实例*来实现这一点。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- Int → List Int
# end Ex
```

通过为上面的实例添加属性 `default_instance` ，我们告诉 Lean 在待解决的类型类综合问题中使用此实例。实际的 Lean 实现定义了同态和异态的算术运算符类型类。此外，`a+b`、`a*b`、`a-b`、`a/b` 和 `a%b` 是异态版本的符号表示。实例 `OfNat Nat n` 是 `OfNat` 类的默认实例（优先级为100）。这就是为什么当期望的类型未知时，数字 `2` 的类型为 `Nat`。您可以定义优先级更高的默认实例来覆盖内置的实例。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
```

优先级对于控制不同默认实例之间的交互也很有用。
例如，假设 `xs` 的类型是 `List α`。在展开 `xs.map (fun x => 2 * x)` 时，我们希望给乘法的同类型实例的优先级高于 `OfNat` 的默认实例。
当我们只实现了 `HMul α α α` 实例而没有实现 `HMul Nat α α` 实例时，这点尤为重要。
现在，我们揭示 Lean 中 `a*b` 表示法的定义。

```lean
# namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
# end Ex
```

`Mul` 类非常方便，适用于只实现均质乘法的类型。

## 局部实例

在 Lean 中，类型类是使用属性来实现的。因此，您可以使用 `local` 修饰符来指示它们仅在当前的 `section` 或 `namespace` 关闭之前有效，或者在当前文件的末尾之前有效。

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

你也可以使用 "``attribute``" 命令来临时禁用一个实例，直到当前 "``section``" 或 "``namespace``" 关闭，或者直到当前文件的末尾。

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

## 作用域实例

你还可以在命名空间中声明作用域实例。这种类型的实例只在你进入该命名空间或打开该命名空间时处于活动状态。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

你可以使用命令 `open scoped <namespace>` 来激活作用域属性，但不会从命名空间中“打开”名称。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
```

## 可判定命题

让我们考虑标准库中另一个示例，即``Decidable``命题的类型类。大致来说，``Prop``类型的一个元素是可判断的，如果我们可以确定它是真还是假。这一区别只在构造性数学中有用；经典数学上，每个命题都是可判定的。但是，如果我们使用经典原理，比如用``case``语句定义一个函数，那么这个函数将不是可计算的。从算法的角度来说，``Decidable``类型类可以用来推断一种有效确定命题是否为真的过程。因此，当可能时，该类型类支持这种计算定义，并同时允许平滑过渡到使用经典定义和经典推理。

在标准库中，``Decidable``被如下形式地定义：

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

从逻辑上讲，拥有一个元素 ``t : Decidable p`` 要比拥有一个元素 ``t : p ∨ ¬p`` 更强大；它使我们能够根据 ``p`` 的真值来定义任意类型的值。例如，为了使表达式 ``if p then a else b`` 有意义，我们需要知道 ``p`` 是可判定的。该表达式是 ``ite p a b`` 的语法糖，其中 ``ite`` 定义如下：

```lean
# namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
# end Hidden
```

标准库还包含一个名为 ``dite`` 的变种，即依赖 if-then-else 表达式。它的定义如下：

```lean
# namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
# end Hidden
```

也就是说，在 ``dite c t e`` 中，我们可以假设在 "then" 分支中 ``hc : c``，在 "else" 分支中 ``hnc : ¬ c``。为了更方便地使用 ``dite``，Lean 允许我们写成 ``if h : c then t else e``，而不是 ``dite c (λ h : c => t) (λ h : ¬ c => e)``。

在没有经典逻辑的情况下，我们不能证明每个命题都是可判定的。但我们可以证明一些命题是可判定的。例如，我们可以证明相等性和自然数和整数上的比较等基本操作的可判定性。此外，可判定性在命题连接词下是保持不变的。

```lean
#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot
```

因此，我们可以对自然数上的可判定谓词进行情况定义：

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

打开隐式参数后，编译器推导出命题 ``x < a ∨ x > b`` 的可判定性，只需应用适当的实例。

使用经典公理，我们可以证明每个命题都是可判定的。您可以导入经典公理，并通过打开 `Classical` 命名空间来使用可判定性的通用实例。

```lean
open Classical
```

因此，``Decidable p``对于每一个``p``都有一个实例。
因此，当您想要进行经典推理时，库中依赖决定性假设的所有定理都可以自由使用。在[章节公理和计算](./axioms_and_computation.md)中，我们将看到使用排中律来定义函数可以阻止它们被用于计算。因此，标准库给`propDecidable`实例分配了较低的优先级。

```lean
# namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
# end Hidden
```

这确保 Lean 会优先考虑其他实例，并在其他推断可决性的尝试失败后再退回到 `propDecidable`。

`Decidable` 类型类还为证明定理提供了一些小规模的自动化。标准库引入了策略 `decide`，它使用 `Decidable` 实例来解决简单的目标。

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
```

它们的工作原理如下。表达式 "decide p" 试图推断一个 "p" 的决策过程，如果成功的话，它的计算结果将是 "true" 或 "false"。特别地，如果 "p" 是一个真闭合表达式，"decide p" 将通过定义化规约为布尔值 "true"。在假设 "decide p = true" 的情况下，"of_decide_eq_true" 得到一个关于 "p" 成立的证明。策略 "decide" 将这一切组合在一起来证明目标 "p"。根据前面的观察，只要推断的决策过程对于 "c" 来说具有足够的信息来定义化地计算出 "isTrue" 的情况，"decide" 将能够成功。

## 管理类型类推断

如果你处于这样一种情况，需要提供一个 Lean 可以通过类型类推断来推断的表达式，你可以使用 "inferInstance" 请求 Lean 执行推断：

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α
```

事实上，你可以使用 Lean 的 ``(t : T)`` 表示法来简洁地指定你要查找的实例所属的类：

```lean
#check (inferInstance : Add Nat)
```

你还可以使用辅助定义 `inferInstanceAs` ：

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α
```

有时候 Lean 无法找到一个实例，因为该类被嵌套在一个定义中。例如，Lean 无法找到 ``Inhabited (Set α)`` 的一个实例。我们可以显式地声明一个：

```lean
def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```

有时，你可能会发现类型类推断无法找到预期的实例，或者更糟糕的是，进入无限循环并超时。为了帮助在这些情况下进行调试，Lean允许你请求搜索的跟踪日志：

```lean
set_option trace.Meta.synthInstance true
```

如果你在使用 VS Code，你可以将鼠标放在相关的定理或定义上来阅读结果，或者使用 ``Ctrl-Shift-Enter`` 快捷键打开消息窗口来阅读结果。在 Emacs 中，你可以使用 ``C-c C-x`` 在你的文件上运行一个独立的 Lean 进程，输出缓冲区会显示每次类型类解析过程被触发时的跟踪。

你还可以使用以下选项限制搜索范围：

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

选项 `synthInstance.maxHeartbeats` 指定每个类型类解析问题的最大心跳数。一个心跳是指（小型）内存分配的次数（以千为单位），0 表示没有限制。选项 `synthInstance.maxSize` 是用于构建类型类实例合成过程中的解决方案时使用的实例的最大数量。

请记住，在 VS Code 和 Emacs 编辑器模式中，``set_option`` 命令中的选项名称支持制表符补全，以帮助您找到合适的选项。

正如上面所述，给定上下文中的类型类实例代表了一个类似 Prolog 的程序，它产生了回溯搜索。程序的效率和找到的解决方案都可能取决于系统尝试实例的顺序。最后声明的实例将首先尝试。而且，如果实例在其他模块中声明，那么它们尝试的顺序将取决于命名空间的打开顺序。后打开的命名空间中声明的实例将先尝试。

您可以通过为类型类实例分配一个 *优先级* 来改变尝试的顺序。当声明一个实例时，它会被分配一个默认的优先级值。您可以在定义实例时分配其他优先级。以下示例说明了如何进行这样的分配：

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

## 使用类型类进行强制转换

最基本的类型强制转换将一个类型的元素映射到另一个类型。例如，从 ``Nat`` 到 ``Int`` 的强制转换允许我们将任意元素 ``n : Nat`` 视为 ``Int`` 类型的元素。但是有些强制转换取决于参数；例如，对于任意类型 ``α``，我们可以将任意元素 ``as : List α`` 视为 ``Set α`` 的元素，即出现在列表中的元素的集合。相应的强制转换定义在以 ``α`` 为参数的类型族 ``List α`` 上。

Lean 允许我们声明三种类型的强制转换：

- 从一个类型族到另一个类型族
- 从一个类型族到排序类的集合
- 从一个类型族到函数类型的集合

第一种类型的强制转换允许我们将源族的任意成员的元素视为目标族相应成员的元素。第二种类型的强制转换允许我们将源族的任意成员的元素视为类型。第三种类型的强制转换允许我们将源族的任意成员的元素视为函数。让我们逐个考虑每种类型。

在 Lean 中，强制转换是基于类型类解析框架实现的。我们通过声明一个类型为 ``Coe α β`` 的实例来定义从 ``α`` 到 ``β`` 的强制转换。例如，我们可以如下方式定义从 ``Bool`` 到 ``Prop`` 的强制转换：

```lean
instance : Coe Bool Prop where
  coe b := b = true
```

这使得我们可以在 if-then-else 表达式中使用布尔条件：

```lean
#eval if true then 5 else 3
#eval if false then 5 else 3
```

我们可以定义从 ``List α`` 到 ``Set α`` 的强制转换如下：

```lean
def list.to_set (l : list α) : set α := λ a, a ∈ l
```

The coercion function `list.to_set` takes a list `l` of type `list α` and returns a function from `α` to `Prop` such that for any element `a` of type `α`, `a` is in `l` if and only if it satisfies the function. This coercion allows us to treat a list as a set and perform set operations on it.

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ List.toSet [2, 3] : Set Nat
```

我们可以使用符号 ``↑`` 来在特定位置引入强制转换的表示。这也有助于明确我们的意图，并解决强制转换解析系统的限制。

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
# def List.toSet : List α → Set α
#   | []    => Set.empty
#   | a::as => {a} ∪ as.toSet
# instance : Coe (List α) (Set α) where
#   coe a := a.toSet
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat
#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat
```

Lean 还支持使用类型类 `CoeDep` 进行依赖的强制转换。例如，我们不能将任意命题强制转换为 `Bool`，只能是实现了 `Decidable` 类型类的命题可以进行强制转换。

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

Lean 还会根据需要链接（非依赖的）强制转换。实际上，类型类 ``CoeT`` 是 ``Coe`` 的传递闭包。

现在我们来考虑第二类强制转换。通过“排序类”，我们指的是宇宙集合 ``Type u``。第二类强制转换的形式为：

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

其中``F``是上述类型族。它使我们可以在``t``为类型``F a1 ... an``时写作``s : t``。换句话说，这个强制转换允许我们将``F a1 ... an``的元素视为类型。这在定义代数结构时非常有用，其中一个组成部分，即结构的载体，是``Type``类型。例如，我们可以如下定义一个半群：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

换句话说，一个半群由一个类型 ``carrier`` 和一个乘法运算 ``mul`` 组成，满足乘法结合律。``instance`` 命令使得我们可以在有 ``a b : S.carrier`` 的情况下，用 ``a * b`` 代替 ``Semigroup.mul S a b``；注意到 Lean 可以从 ``a`` 和 ``b`` 的类型推断出参数 ``S``。函数 ``Semigroup.carrier`` 将类 ``Semigroup`` 映射到排序 ``Type u``：

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
#check Semigroup.carrier
```

如果我们声明这个函数为一个强制转换函数，那么每当我们有一个半群``S：Semigroup``时，我们可以使用``a：S``来代替``a：S.carrier``：

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

是强制转换使得 ``(a b c : S)`` 的写法成为可能。注意，我们定义了一个 ``CoeSort Semigroup (Type u)`` 的实例而不是 ``Coe Semigroup (Type u)``。

通过“类函数类型”，我们指的是 Pi 类型 ``(z : B) → C`` 的集合。第三种强制转换的形式为：

```
    c : (x1 : A1) → ... → (xn : An) → (y : F x1 ... xn) → (z : B) → C
```

其中``F``再次是类型的一个族，而``B``和``C``可以依赖于``x1, ..., xn, y``。这使得当``t``是``F a1 ... an``的元素时，我们可以写成``t s``。换句话说，强制转换使我们能够将``F a1 ... an``的元素视为函数。继续上面的例子，我们可以定义半群``S1``和``S2``之间的态射的概念。也就是说，从``S1``的承载到``S2``的承载的函数（注意隐式的强制转换），并且保持乘法运算。投影``morphism.mor``将一个态射映射到底层的函数：

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```

因此，它是第三种类型的强制的首要选择。

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
# structure Morphism (S1 S2 : Semigroup) where
#   mor : S1 → S2
#   resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
```

有了强制转换的设定，我们可以使用 ``f (a * a * a)`` 来代替 ``f.mor (a * a * a)``。当使用 ``Morphism`` ``f`` 替代期望函数的地方时，Lean会插入强制转换。与 ``CoeSort`` 类似，我们还有另一个类 ``CoeFun`` 用于这种类型的强制转换。字段 ``F`` 用于指定我们要转换到的函数类型。该类型可能依赖于我们要转换的类型。