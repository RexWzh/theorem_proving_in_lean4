结构和记录
======================

我们已经看到 Lean 的基础系统包括归纳类型。此外，我们还注意到一个引人注目的事实是，仅仅基于类型宇宙、依赖箭头类型和归纳类型就可以构建一个重要的数学建筑；其他一切都可以从这些基础出发推导出来。Lean 标准库包含许多归纳类型的实例（例如 `Nat`、`Prod`、`List`），甚至连逻辑连词也是使用归纳类型定义的。

回想一下，一个只包含一个构造器的非递归归纳类型被称为*结构*或*记录*。乘积类型是一个结构，依赖乘积（Sigma）类型也是一个结构。一般来说，当我们定义一个结构 `S` 时，我们通常会定义*投影*函数，以允许我们“解构”每个 `S` 的实例并检索存储在其字段中的值。函数 `prod.fst` 和 `prod.snd` 返回对的第一个和第二个元素，就是这样的投影函数的例子。

在编写程序或形式化数学时，定义包含许多字段的结构是很常见的。在 Lean 中可以使用 `structure` 命令提供的基础设施来支持这个过程。当我们使用这个命令定义一个结构时，Lean 会自动生成所有的投影函数。`structure` 命令还允许我们基于先前定义的结构定义新的结构。此外，Lean 还提供了方便的符号来定义给定结构的实例。

声明结构
--------------------

`structure` 命令本质上是定义归纳数据类型的"前端"。每个 `structure` 声明都引入了一个同名的命名空间。一般形式如下：

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

大多数部分是可选的。以下是一个例子：

```lean
structure Point (α : Type u) where
  mk :: (x : α) (y : α)
```

类型 ``Point`` 的值是通过使用 ``Point.mk a b`` 创建的，可以使用 ``Point.x p`` 和 ``Point.y p`` 来访问点 ``p`` 的字段（但 `p.x` 和 `p.y` 也有效，详情见下文）。结构命令还会生成有用的递归器和定理。以下是对上面声明生成的一些构造。

```lean
# structure Point (α : Type u) where
#  mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection
```

如果没有提供构造函数的名称，则默认名称为 ``mk``。如果在每个字段之间添加换行符，则还可以避免在字段名称周围使用括号。

```lean
structure Point (α : Type u) where
  x : α
  y : α
```

下面是一些使用生成的构造的简单定理和表达式。如同往常，您可以使用命令“open Point”来避免使用前缀“Point”。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```

给定``p : Point Nat``，点符号表示``p.x``是``Point.x p``的缩写。这提供了一种方便的方法来访问结构体的字段。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

点符号表示法不仅方便访问记录的投影，还方便应用与同名命名空间中定义的函数。回想一下，在[连接词](./propositions_and_proofs.md#conjunction)部分中，如果 ``p`` 的类型是 ``Point``，那么表达式 ``p.foo`` 的解释是 ``Point.foo p``，假设 ``foo`` 的第一个非隐式参数的类型是 ``Point``。因此，在下面的示例中，表达式 ``p.add q`` 是 ``Point.add p q`` 的简写形式。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
```

在下一章中，你将学习如何定义一个像 ``add`` 这样的函数，使它可以适用于 ``Point α`` 的元素，而不仅仅是 ``Point Nat``，前提是 ``α`` 有一个关联的加法操作。

更一般地，给定表达式 ``p.foo x y z``，其中 `p : Point`，Lean会将 ``p`` 插入到类型为 ``Point`` 的 ``Point.foo`` 的第一个参数位置。例如，对于下面的标量乘法定义，``p.smul 3`` 被解释为 ``Point.smul 3 p``。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#  deriving Repr
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}
```

通常可以使用类似的技巧来处理 ``List.map`` 函数，它将列表作为其第二个非隐式参数传入：

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]
```

**对象**

我们一直在使用构造函数来创建结构类型的元素。对于包含多个字段的结构体来说，这种方式通常很不方便，因为我们必须记住字段定义的顺序。因此，Lean提供了以下用于定义结构类型元素的替代符号表示法。

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

当结构体的名称可以从预期的类型中推断出时，后缀 ``: structure-type`` 可以省略。例如，我们使用这种记法来定义“点”。字段的指定顺序不重要，所以下面的所有表达式都定义了相同的点。

* * *

```lisp
(define-struct point (x y))
```

这个定义创建了一个带有两个字段 ``x`` 和 ``y`` 的结构体。我们可以使用以下表达式来创建一个点：

```lisp
(make-point 1 2)
```

这会创建一个 ``x`` 值为 1，``y`` 值为 2 的点。这个点的类型是 ``point``。

我们可以通过以下方式来访问点的字段：

```lisp
(point-x (make-point 1 2)) ;; 返回 1
(point-y (make-point 1 2)) ;; 返回 2
```

使用辅助函数 ``point-x`` 和 ``point-y`` 可以返回一个点的 ``x`` 和 ``y`` 值。

注意，由于结构体的名称可以从预期的类型中推断出，所以我们可以省略结构体类型的后缀 ``: point``。下面的代码与上面的代码等效：

```lisp
(define-struct point (x y))
(define (make x y) (make-point x y))
(define (x p) (point-x p))
(define (y p) (point-y p))

(make 1 2) ;; 返回一个点
(x (make 1 2)) ;; 返回 1
(y (make 1 2)) ;; 返回 2
```

这种推断结构体名称的能力使得我们定义和使用结构体变得更加简洁和方便。

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- Point ℕ
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat)

example : Point Nat :=
  { y := 20, x := 10 }
```

如果未指定字段的值，Lean 尝试推断它。如果无法推断未指定的字段，Lean 将发出错误提醒，指示无法合成相应的占位符。

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

*记录更新*是另一个常见操作，它通过修改旧记录对象中的一个或多个字段的值来创建一个新的记录对象。Lean允许您在记录的规范中指定未分配的字段应该从先前定义的结构对象``s``中获取，方法是在字段赋值之前添加注释``s with``。如果提供了多个记录对象，则会按顺序访问它们，直到找到一个包含未指定字段的对象。如果在访问所有对象之后仍然存在未指定的字段名，Lean将引发错误。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

继承
-----------

我们可以通过添加新字段来扩展现有的结构。这个特性可以模拟一种继承的形式。

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

在下面的例子中，我们使用多重继承来定义一个结构，并使用父结构的对象来定义一个对象。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```

