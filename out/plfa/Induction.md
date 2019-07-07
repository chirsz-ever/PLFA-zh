---
src       : src/plfa/Induction.lagda
title     : "Induction: 归纳证明"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
translators : ["Oling Cat"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="185" class="Keyword">module</a> <a id="192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}" class="Module">plfa.Induction</a> <a id="207" class="Keyword">where</a>{% endraw %}</pre>

{::comment}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf
{:/}

> 归纳会让你对无中生有感到内疚
> ... 但它却是文明中最伟大的思想之一。
> -- Herbert Wilf

{::comment}
Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.
{:/}

现在我们定义了自然数及其运算，下一步是学习如何证明它们满足的性质。如其名称所示，**归纳数据类型（inductive datatype）**是通过**归纳（induction）**来证明的。

{::comment}
## Imports
{:/}

## 导入

{::comment}
We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{:/}

我们需要上一章中的相等性，加上自然数及其运算。我们还导入了一些新的运算：
`cong`、`sym` 和 `_≡⟨_⟩_`，之后会解释它们：

<pre class="Agda">{% raw %}<a id="1122" class="Keyword">import</a> <a id="1129" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1167" class="Symbol">as</a> <a id="1170" class="Module">Eq</a>
<a id="1173" class="Keyword">open</a> <a id="1178" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1181" class="Keyword">using</a> <a id="1187" class="Symbol">(</a><a id="1188" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="1191" class="Symbol">;</a> <a id="1193" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="1197" class="Symbol">;</a> <a id="1199" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="1203" class="Symbol">;</a> <a id="1205" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="1208" class="Symbol">)</a>
<a id="1210" class="Keyword">open</a> <a id="1215" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a> <a id="1230" class="Keyword">using</a> <a id="1236" class="Symbol">(</a><a id="1237" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin_</a><a id="1243" class="Symbol">;</a> <a id="1245" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">_≡⟨⟩_</a><a id="1250" class="Symbol">;</a> <a id="1252" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">_≡⟨_⟩_</a><a id="1258" class="Symbol">;</a> <a id="1260" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">_∎</a><a id="1262" class="Symbol">)</a>
<a id="1264" class="Keyword">open</a> <a id="1269" class="Keyword">import</a> <a id="1276" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="1285" class="Keyword">using</a> <a id="1291" class="Symbol">(</a><a id="1292" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1293" class="Symbol">;</a> <a id="1295" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="1299" class="Symbol">;</a> <a id="1301" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="1304" class="Symbol">;</a> <a id="1306" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="1309" class="Symbol">;</a> <a id="1311" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="1314" class="Symbol">;</a> <a id="1316" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="1319" class="Symbol">)</a>{% endraw %}</pre>


{::comment}
## Properties of operators
{:/}

## 运算符的性质

{::comment}
Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.
{:/}

运算符总是到处出现，而数学家们已经统一了一些最常见的性质的名称。

{::comment}
* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.
{:/}

* **幺元（Identity）**。对于所有的 `n`，若 `0 + n ≡ n`，则 `+` 有左幺元 `0`；
  若 `n + 0 ≡ n`，则 `+` 有右幺元 `0`。同时为左幺元和右幺元的值称简称幺元。
  幺元有时也称作**单位元（Unit）**。

* **结合律（Associativity）**。若括号的位置无关紧要，则称运算符 `+` 满足结合律，
  即对于所有的 `m`、`n` 和 `p`，有 `(m + n) + p ≡ m + (n + p)`。

* **交换律（Commutativity）**。若参数的位置无关紧要，则称运算符 `+` 满足交换律，
  即对于所有的 `m` 和 `n`，有 `m + n ≡ n + m`。

* **分配率（Distributivity）**。对于所有的 `m`、`n` 和 `p`，若
  `(m + n) * p ≡ (m * p) + (n * p)`，则运算符 `*` 对运算符 `+` 满足左分配率；
  对于所有的 `m`、`n` 和 `p`，若 `m * (p + q) ≡ (m * p) + (m * q)`，则满足右分配率。

{::comment}
Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.
{:/}

加法的幺元为 `0`，乘法的幺元为 `1`，加法和乘法都满足结合律和交换律，乘法对加法满足分配率。

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

如果你在一个舞会上碰见了一位操作员，那么你可以跟他闲聊，问问他是否有单位元，能不能结合或者交换。如果你碰见了两位操作员，那么可以问他们某一位是否在另一位上面分布。
（作者的双关冷笑话，运算符（Operator）也有操作员的意思= =||）

{::comment}
Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.
{:/}

正经来说，如果你在阅读技术论文时遇到了一个运算符，那么你可以考察它是否拥有一个幺元，是否满足结合律或分配率，或者是否对另一个运算符满足分配率，这能为你提供一种视角。细心的作者通常会指出它们是否满足这些性质，比如说指明一个新引入的运算符满足结合率但不满足交换率。

{::comment}
#### Exercise `operators` {#operators}
{:/}

#### 练习：`operators` {#operators}

{::comment}
Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
{:/}

请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配率。

{::comment}
<pre class="Agda">{% raw %}<a id="4331" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="4384" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
Give an example of an operator that has an identity and is
associative but is not commutative.
{:/}

请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。


{::comment}
## Associativity
{:/}

## 结合律

{::comment}
One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:
{:/}

加法的一个性质是满足**结合律**，即括号的位置无关紧要：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `m`, `n`, and `p` are variables that range over all natural numbers.
{:/}

这里的 `m`、`n` 和 `p` 都是取值范围是全体自然数的变量。

{::comment}
We can test the proposition by choosing specific numbers for the three
variables:
{:/}

我们可以为这三个变量选取特定的数值来测试此命题：

<pre class="Agda">{% raw %}<a id="5063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5063" class="Function">_</a> <a id="5065" class="Symbol">:</a> <a id="5067" class="Symbol">(</a><a id="5068" class="Number">3</a> <a id="5070" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5072" class="Number">4</a><a id="5073" class="Symbol">)</a> <a id="5075" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5077" class="Number">5</a> <a id="5079" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5081" class="Number">3</a> <a id="5083" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5085" class="Symbol">(</a><a id="5086" class="Number">4</a> <a id="5088" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5090" class="Number">5</a><a id="5091" class="Symbol">)</a>
<a id="5093" class="Symbol">_</a> <a id="5095" class="Symbol">=</a>
  <a id="5099" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="5109" class="Symbol">(</a><a id="5110" class="Number">3</a> <a id="5112" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5114" class="Number">4</a><a id="5115" class="Symbol">)</a> <a id="5117" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5119" class="Number">5</a>
  <a id="5123" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="5131" class="Number">7</a> <a id="5133" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5135" class="Number">5</a>
  <a id="5139" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="5147" class="Number">12</a>
  <a id="5152" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="5160" class="Number">3</a> <a id="5162" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5164" class="Number">9</a>
  <a id="5168" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="5176" class="Number">3</a> <a id="5178" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5180" class="Symbol">(</a><a id="5181" class="Number">4</a> <a id="5183" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5185" class="Number">5</a><a id="5186" class="Symbol">)</a>
  <a id="5190" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.
{:/}

在这里，我们将计算过程写成了等式链，一行一个式子。这样的等式链通常非常易读，你可以从上到下，直到遇到最简形式（本例中为 `12`），也可以从下到上，直到回到同样的式子。

{::comment}
The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?
{:/}

该测试揭示了结合律可能没有它初看起来那么显然。为什么 `7 + 5` 与 `3 + 9` 相同？我们可能需要收集更多证据，选择其它的数值来测试此命题。但由于自然数是无限的，因此测试永远无法完成。那么我们还有其它可以确保结合律对于**所有**自然数都成立的方法吗？

{::comment}
The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.
{:/}

答案是肯定的！我们可以用**归纳证明（Proof by Induction）**来确保某个性质对于所有的自然数都成立。


{::comment}
## Proof by induction
{:/}

## 归纳证明

{::comment}
Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.
{:/}

回想自然数的定义，它由一个**起始步骤**「`zero` 是一个自然数」
和一个**归纳步骤**「若 `m` 是一个自然数，则 `suc m` 也是一个自然数」构成。

{::comment}
Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.
{:/}

归纳证明遵循此定义的结构。要通过归纳证明自然数的某个性质，我们需要两个步骤。其一是**起始步骤**，我们需要证明此性质对 `zero` 成立。其二是**归纳步骤**，我们假设此性质对一个任意自然数 `m` 成立（我们称之为**归纳假设（Induction
Hypothesis）**），然后证明该性质对 `suc m` 必定成立。

{::comment}
If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:
{:/}

若我们将 `m` 的某种性质（Property）写作 `P m`，那么我们需要证明的就是以下两个推导规则：

    ------
    P zero

    P m
    ---------
    P (suc m)

{::comment}
Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.
{:/}

我们来分析一下这些规则。第一条规则是起始步骤，它需要我们证明性质 `P` 对 `zero`
成立。第二条规则是归纳步骤，它需要我们证明若归纳假设「`P` 对 `m` 成立」，那么 `P` 也对 `suc m` 成立。

{::comment}
Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:
{:/}

为什么它能够起作用？同样，它也可以用创世故事来讲解。在最开始，我们对性质一无所知：


{::comment}
    -- In the beginning, no properties are known.
{:/}

    -- 起初，世上没有已知的性质。

{::comment}
Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:
{:/}

现在我们对所有已知的性质应用上述两条规则。起始步骤告诉我们 `P zero` 成立，所以我们将它加入已知的性质集合中。归纳步骤告诉我们若（在昨天）`P m` 成立，那么（在今天）`P (suc m)` 也成立。我们在今天之前并不知道任何性质，因此归纳步骤在这里不适用：

{::comment}
    -- On the first day, one property is known.
    P zero
{:/}

    -- 第一天，我们知道了一个性质。
    P zero

{::comment}
Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:
{:/}

然后我们重复此过程。在接下来的一天我们知道今天之前的所有性质，以及任何通过此规则添加的性质。起始步骤告诉我们 `P zero`
成立，当然我们已经知道这件事了。而如今归纳步骤告诉我们，由于 `P zero`
在昨天成立，那么 `P (suc zero)` 今天也成立。

{::comment}
    -- On the second day, two properties are known.
    P zero
    P (suc zero)
{:/}

    -- 第二天，我们知道了两个性质。
    P zero
    P (suc zero)

{::comment}
And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:
{:/}

我们再重复此过程。现在归纳步骤告诉我们由于 `P zero` 和 `P (suc zero)` 都成立，因此 `P (suc zero)` 和 `P (suc (suc zero))` 也成立。我们已经知道第一个成立了，但第二个是新引入的：

{::comment}
    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
{:/}

    -- 第三天，我们知道了三个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))
{:/}

    -- 第四天，我们知道了四个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

{::comment}
The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.
{:/}

此过程可以继续下去。在第 **n** 天会有 **n** 个不同的性质成立。每个自然数的性质都会在某一天出现。具体来说，性质 `P n` 会在第 **n+1** 天首次出现。


{::comment}
## Our first proof: associativity
{:/}

## 第一个证明：结合律

{::comment}
To prove associativity, we take `P m` to be the property:
{:/}

要证明结合律，我们需要将 `P m` 看做以下性质：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:
{:/}

这里的 `n` 和 `p` 是任意自然数，因此若我们可以证明该等式对所有的 `m`
都成立，那么它也会对所有的 `n` 和 `p` 成立。其推理规则的对应实例如下：

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
If we can demonstrate both of these, then associativity of addition
follows by induction.
{:/}

如果我们可以证明这两条规则，那么加法结合律就可根据归纳法来证明。

{::comment}
Here is the proposition's statement and proof:
{:/}

以下为此性质的陈述和证明：

<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="11564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="11572" class="Symbol">:</a> <a id="11574" class="Symbol">∀</a> <a id="11576" class="Symbol">(</a><a id="11577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11577" class="Bound">m</a> <a id="11579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11579" class="Bound">n</a> <a id="11581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11581" class="Bound">p</a> <a id="11583" class="Symbol">:</a> <a id="11585" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11586" class="Symbol">)</a> <a id="11588" class="Symbol">→</a> <a id="11590" class="Symbol">(</a><a id="11591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11577" class="Bound">m</a> <a id="11593" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11579" class="Bound">n</a><a id="11596" class="Symbol">)</a> <a id="11598" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11581" class="Bound">p</a> <a id="11602" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11577" class="Bound">m</a> <a id="11606" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11608" class="Symbol">(</a><a id="11609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11579" class="Bound">n</a> <a id="11611" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11581" class="Bound">p</a><a id="11614" class="Symbol">)</a>
<a id="11616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="11624" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11629" class="Bound">n</a> <a id="11631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11631" class="Bound">p</a> <a id="11633" class="Symbol">=</a>
  <a id="11637" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="11647" class="Symbol">(</a><a id="11648" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11653" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11629" class="Bound">n</a><a id="11656" class="Symbol">)</a> <a id="11658" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11631" class="Bound">p</a>
  <a id="11664" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11629" class="Bound">n</a> <a id="11674" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11631" class="Bound">p</a>
  <a id="11680" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
   <a id="11687" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11692" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11694" class="Symbol">(</a><a id="11695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11629" class="Bound">n</a> <a id="11697" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11631" class="Bound">p</a><a id="11700" class="Symbol">)</a>
  <a id="11704" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="11706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="11714" class="Symbol">(</a><a id="11715" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a><a id="11720" class="Symbol">)</a> <a id="11722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a> <a id="11724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a> <a id="11726" class="Symbol">=</a>
  <a id="11730" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="11740" class="Symbol">(</a><a id="11741" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11747" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a><a id="11750" class="Symbol">)</a> <a id="11752" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a>
  <a id="11758" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11766" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11770" class="Symbol">(</a><a id="11771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11773" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a><a id="11776" class="Symbol">)</a> <a id="11778" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a>
  <a id="11784" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11792" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11796" class="Symbol">((</a><a id="11798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11800" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a><a id="11803" class="Symbol">)</a> <a id="11805" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a><a id="11808" class="Symbol">)</a>
  <a id="11812" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="11815" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="11820" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11824" class="Symbol">(</a><a id="11825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="11833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a> <a id="11837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a><a id="11838" class="Symbol">)</a> <a id="11840" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="11846" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11850" class="Symbol">(</a><a id="11851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11853" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11855" class="Symbol">(</a><a id="11856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a> <a id="11858" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a><a id="11861" class="Symbol">))</a>
  <a id="11866" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11874" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11719" class="Bound">m</a> <a id="11880" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11882" class="Symbol">(</a><a id="11883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11722" class="Bound">n</a> <a id="11885" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11724" class="Bound">p</a><a id="11888" class="Symbol">)</a>
  <a id="11892" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.
{:/}

我们将此证明命名为 `+-assoc`。在 Agda 中，标识符可以由除空格或 `@.(){};_`
之外的任何字符序列构成。

{::comment}
Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:
{:/}

我们来分析一下这段代码。其签名（Signature）描述了我们定义的标识符 `+-assoc`
为以下命题提供了证据（Evidence）：

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.
{:/}

倒 A 符号读作「对于所有（for all）」，而该命题断言对于所有的自然数 `m`、`n`
和 `p`，等式 `(m + n) + p ≡ m + (n + p)` 成立。该命题的证据是一个接受三个自然数的函数，将它们绑定到 `m`、`n` 和 `p`，并返回该等式对应实例的证据。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

用加法的起始步骤化简等式两边会得到：

    n + p ≡ n + p

{::comment}
This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.
{:/}

此式平凡成立。阅读此证明中起始步骤中的等式链，其最初和最末的式子分别匹配待证等式的两边，从上到下或从下到上读都会让我们在中间遇到 `n + p` 。此步骤除了化简外不需要任何依据。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

用加法的归纳步骤化简等式两边会得到：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    (m + n) + p ≡ m + (n + p)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:
{:/}

阅读此证明中归纳步骤的等式链，其最初和最末的式子分别匹配待证等式的两边，从上到下或从下到上读都会让我们到达上面化简等式的地方。剩下的等式，不止用化简就行，因此我们需要为推理链使用一个附加的运算符 `_≡⟨_⟩_`，为等式给出的依据会放在尖括号中。这里给出的依据是：

    ⟨ cong suc (+-assoc m n p) ⟩

{::comment}
Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.
{:/}

在这里，递归调用的 `+-assoc m n p` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。

{::comment}
A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.
{:/}

若某个关系在应用给定函数后仍然保持不变，则称该关系满足**合同性（Congruence）**。若 `e` 是 `x ≡ y` 的证据，那么对于任意函数 `f`，`cong f e` 是 `f x ≡ f y` 的证据。

{::comment}
Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well-founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.
{:/}

在这里并未假定归纳假设，而是通过递归调用我们定义的函数 `+-assoc m n p` 来证明。对于加法，这是良基的（well-founded），因为更大数值的结合律可基于更小数值的结合律来证明。在此步骤中，`assoc (suc m) n p` 是用 `assoc m n p` 证明的。归纳证明和递归定义之间的这种对应是 Agda 中最吸引人的方面之一。

{::comment}
## Induction as recursion
{:/}

## 归纳即递归

下面是归纳如何对应于递归的具体例子，它是在结合律的证明中，将 `m` 实例化为 `2`
时出现的计算。

<pre class="Agda">{% raw %}<a id="+-assoc-2"></a><a id="16062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16062" class="Function">+-assoc-2</a> <a id="16072" class="Symbol">:</a> <a id="16074" class="Symbol">∀</a> <a id="16076" class="Symbol">(</a><a id="16077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16077" class="Bound">n</a> <a id="16079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16079" class="Bound">p</a> <a id="16081" class="Symbol">:</a> <a id="16083" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16084" class="Symbol">)</a> <a id="16086" class="Symbol">→</a> <a id="16088" class="Symbol">(</a><a id="16089" class="Number">2</a> <a id="16091" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16077" class="Bound">n</a><a id="16094" class="Symbol">)</a> <a id="16096" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16079" class="Bound">p</a> <a id="16100" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16102" class="Number">2</a> <a id="16104" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16106" class="Symbol">(</a><a id="16107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16077" class="Bound">n</a> <a id="16109" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16079" class="Bound">p</a><a id="16112" class="Symbol">)</a>
<a id="16114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16062" class="Function">+-assoc-2</a> <a id="16124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a> <a id="16126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a> <a id="16128" class="Symbol">=</a>
  <a id="16132" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="16142" class="Symbol">(</a><a id="16143" class="Number">2</a> <a id="16145" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a><a id="16148" class="Symbol">)</a> <a id="16150" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a>
  <a id="16156" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="16164" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16168" class="Symbol">(</a><a id="16169" class="Number">1</a> <a id="16171" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a><a id="16174" class="Symbol">)</a> <a id="16176" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a>
  <a id="16182" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="16190" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16194" class="Symbol">((</a><a id="16196" class="Number">1</a> <a id="16198" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a><a id="16201" class="Symbol">)</a> <a id="16203" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a><a id="16206" class="Symbol">)</a>
  <a id="16210" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="16213" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="16218" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16222" class="Symbol">(</a><a id="16223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16298" class="Function">+-assoc-1</a> <a id="16233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a> <a id="16235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a><a id="16236" class="Symbol">)</a> <a id="16238" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="16244" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16248" class="Symbol">(</a><a id="16249" class="Number">1</a> <a id="16251" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16253" class="Symbol">(</a><a id="16254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a> <a id="16256" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a><a id="16259" class="Symbol">))</a>
  <a id="16264" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="16272" class="Number">2</a> <a id="16274" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16276" class="Symbol">(</a><a id="16277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16124" class="Bound">n</a> <a id="16279" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16126" class="Bound">p</a><a id="16282" class="Symbol">)</a>
  <a id="16286" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
  <a id="16290" class="Keyword">where</a>
  <a id="16298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16298" class="Function">+-assoc-1</a> <a id="16308" class="Symbol">:</a> <a id="16310" class="Symbol">∀</a> <a id="16312" class="Symbol">(</a><a id="16313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16313" class="Bound">n</a> <a id="16315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16315" class="Bound">p</a> <a id="16317" class="Symbol">:</a> <a id="16319" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16320" class="Symbol">)</a> <a id="16322" class="Symbol">→</a> <a id="16324" class="Symbol">(</a><a id="16325" class="Number">1</a> <a id="16327" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16313" class="Bound">n</a><a id="16330" class="Symbol">)</a> <a id="16332" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16315" class="Bound">p</a> <a id="16336" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16338" class="Number">1</a> <a id="16340" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16342" class="Symbol">(</a><a id="16343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16313" class="Bound">n</a> <a id="16345" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16315" class="Bound">p</a><a id="16348" class="Symbol">)</a>
  <a id="16352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16298" class="Function">+-assoc-1</a> <a id="16362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a> <a id="16364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a> <a id="16366" class="Symbol">=</a>
    <a id="16372" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
      <a id="16384" class="Symbol">(</a><a id="16385" class="Number">1</a> <a id="16387" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a><a id="16390" class="Symbol">)</a> <a id="16392" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a>
    <a id="16400" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="16410" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16414" class="Symbol">(</a><a id="16415" class="Number">0</a> <a id="16417" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a><a id="16420" class="Symbol">)</a> <a id="16422" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a>
    <a id="16430" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="16440" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16444" class="Symbol">((</a><a id="16446" class="Number">0</a> <a id="16448" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a><a id="16451" class="Symbol">)</a> <a id="16453" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a><a id="16456" class="Symbol">)</a>
    <a id="16462" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="16465" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="16470" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16474" class="Symbol">(</a><a id="16475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16562" class="Function">+-assoc-0</a> <a id="16485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a> <a id="16487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a><a id="16488" class="Symbol">)</a> <a id="16490" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
      <a id="16498" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16502" class="Symbol">(</a><a id="16503" class="Number">0</a> <a id="16505" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16507" class="Symbol">(</a><a id="16508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a> <a id="16510" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a><a id="16513" class="Symbol">))</a>
    <a id="16520" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="16530" class="Number">1</a> <a id="16532" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16534" class="Symbol">(</a><a id="16535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16362" class="Bound">n</a> <a id="16537" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16364" class="Bound">p</a><a id="16540" class="Symbol">)</a>
    <a id="16546" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
    <a id="16552" class="Keyword">where</a>
    <a id="16562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16562" class="Function">+-assoc-0</a> <a id="16572" class="Symbol">:</a> <a id="16574" class="Symbol">∀</a> <a id="16576" class="Symbol">(</a><a id="16577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16577" class="Bound">n</a> <a id="16579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16579" class="Bound">p</a> <a id="16581" class="Symbol">:</a> <a id="16583" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16584" class="Symbol">)</a> <a id="16586" class="Symbol">→</a> <a id="16588" class="Symbol">(</a><a id="16589" class="Number">0</a> <a id="16591" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16577" class="Bound">n</a><a id="16594" class="Symbol">)</a> <a id="16596" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16579" class="Bound">p</a> <a id="16600" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16602" class="Number">0</a> <a id="16604" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16606" class="Symbol">(</a><a id="16607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16577" class="Bound">n</a> <a id="16609" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16579" class="Bound">p</a><a id="16612" class="Symbol">)</a>
    <a id="16618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16562" class="Function">+-assoc-0</a> <a id="16628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16628" class="Bound">n</a> <a id="16630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16630" class="Bound">p</a> <a id="16632" class="Symbol">=</a>
      <a id="16640" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
        <a id="16654" class="Symbol">(</a><a id="16655" class="Number">0</a> <a id="16657" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16628" class="Bound">n</a><a id="16660" class="Symbol">)</a> <a id="16662" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16630" class="Bound">p</a>
      <a id="16672" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
        <a id="16684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16628" class="Bound">n</a> <a id="16686" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16630" class="Bound">p</a>
      <a id="16696" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
        <a id="16708" class="Number">0</a> <a id="16710" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16712" class="Symbol">(</a><a id="16713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16628" class="Bound">n</a> <a id="16715" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16630" class="Bound">p</a><a id="16718" class="Symbol">)</a>
      <a id="16726" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>


{::comment}
## Terminology and notation
{:/}

## 术语与记法

{::comment}
The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}{% link out/plfa/Quantifiers.md%}).
{:/}

在结合律的陈述中出现的符号 `∀` 表示它对于所有的 `m`、`n` 和 `p` 都成立。我们将 `∀` 称为**全称量词**（Universal Quantifier），我们会在
[Quantifiers]({{ site.baseurl }}{% link out/plfa/Quantifiers.md%}) 章节中进一步讨论。

{::comment}
Evidence for a universal quantifier is a function.  The notations
{:/}

全称量词的证据是一个函数。记法

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
and
{:/}

和

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with the each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.
{:/}

是等价的。它们不同于像 `ℕ → ℕ → ℕ` 这样的函数类型，其中的变量与每一个实参类型相关联，其结果类型可能会涉及（或依赖于）这些变量，因此它们叫做**依赖函数**（Dependent Function）。


{::comment}
## Our second proof: commutativity
{:/}

## 第二个证明：交换律

{::comment}
Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:
{:/}

加法的另一个重要性质是**交换律（Commutativity）**，即运算数的顺序无关紧要：

    m + n ≡ n + m

{::comment}
The proof requires that we first demonstrate two lemmas.
{:/}

要证明它，我们需要先证明两条引理（Lemma）。

{::comment}
### The first lemma
{:/}

### 第一条引理

{::comment}
The base case of the definition of addition states that zero
is a left-identity:
{:/}

加法定义的起始步骤说明零是一个左幺元：

    zero + n ≡ n

{::comment}
Our first lemma states that zero is also a right-identity:
{:/}

我们的第一条引理则说明零也是一个右幺元：

    m + zero ≡ m

{::comment}
Here is the lemma's statement and proof:
{:/}

以下是此引理的证明：

<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="18584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18584" class="Function">+-identityʳ</a> <a id="18596" class="Symbol">:</a> <a id="18598" class="Symbol">∀</a> <a id="18600" class="Symbol">(</a><a id="18601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18601" class="Bound">m</a> <a id="18603" class="Symbol">:</a> <a id="18605" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18606" class="Symbol">)</a> <a id="18608" class="Symbol">→</a> <a id="18610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18601" class="Bound">m</a> <a id="18612" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18614" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18619" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18601" class="Bound">m</a>
<a id="18623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18584" class="Function">+-identityʳ</a> <a id="18635" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18640" class="Symbol">=</a>
  <a id="18644" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="18654" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18659" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18661" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="18668" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="18676" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="18683" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="18685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18584" class="Function">+-identityʳ</a> <a id="18697" class="Symbol">(</a><a id="18698" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18702" class="Bound">m</a><a id="18703" class="Symbol">)</a> <a id="18705" class="Symbol">=</a>
  <a id="18709" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="18719" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18702" class="Bound">m</a> <a id="18725" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18727" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="18734" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="18742" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18746" class="Symbol">(</a><a id="18747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18702" class="Bound">m</a> <a id="18749" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18751" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="18755" class="Symbol">)</a>
  <a id="18759" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="18762" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="18767" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18771" class="Symbol">(</a><a id="18772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18584" class="Function">+-identityʳ</a> <a id="18784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18702" class="Bound">m</a><a id="18785" class="Symbol">)</a> <a id="18787" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="18793" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18702" class="Bound">m</a>
  <a id="18801" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:
{:/}

其签名描述了我们定义的标识符 `+-identityʳ` 提供了以下命题的证据：

    ∀ (m : ℕ) → m + zero ≡ m

{::comment}
Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受一个自然数，将其绑定到 `m`，然后返回该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + zero ≡ zero

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很直白。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m) + zero = suc m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + zero) = suc m

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + zero ≡ m

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:
{:/}

阅读此等式链，从上到下和从下到上读都会让我们到达上面化简等式的地方。剩下的等式可由以下依据得出：

    ⟨ cong suc (+-identityʳ m) ⟩

{::comment}
Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.
{:/}

在这里，递归调用的 `+-identityʳ m` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第一条引理证毕。

{::comment}
### The second lemma
{:/}

### 第二条引理

{::comment}
The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:
{:/}

加法定义的归纳步骤将第一个参数的 `suc` 推到了外面：

    suc m + n ≡ suc (m + n)

{::comment}
Our second lemma does the same for `suc` on the second argument:
{:/}

我们的第二条引理则对第二个参数的 `suc` 做同样的事情：

    m + suc n ≡ suc (m + n)

{::comment}
Here is the lemma's statement and proof:
{:/}

下面是该引理的陈述和证明：

<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="20919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20919" class="Function">+-suc</a> <a id="20925" class="Symbol">:</a> <a id="20927" class="Symbol">∀</a> <a id="20929" class="Symbol">(</a><a id="20930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20930" class="Bound">m</a> <a id="20932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20932" class="Bound">n</a> <a id="20934" class="Symbol">:</a> <a id="20936" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20937" class="Symbol">)</a> <a id="20939" class="Symbol">→</a> <a id="20941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20930" class="Bound">m</a> <a id="20943" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20945" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20932" class="Bound">n</a> <a id="20951" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="20953" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20957" class="Symbol">(</a><a id="20958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20930" class="Bound">m</a> <a id="20960" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20932" class="Bound">n</a><a id="20963" class="Symbol">)</a>
<a id="20965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20919" class="Function">+-suc</a> <a id="20971" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20976" class="Bound">n</a> <a id="20978" class="Symbol">=</a>
  <a id="20982" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="20992" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20997" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20999" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20976" class="Bound">n</a>
  <a id="21007" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="21015" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20976" class="Bound">n</a>
  <a id="21023" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="21031" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21035" class="Symbol">(</a><a id="21036" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="21041" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20976" class="Bound">n</a><a id="21044" class="Symbol">)</a>
  <a id="21048" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="21050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20919" class="Function">+-suc</a> <a id="21056" class="Symbol">(</a><a id="21057" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a><a id="21062" class="Symbol">)</a> <a id="21064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a> <a id="21066" class="Symbol">=</a>
  <a id="21070" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="21080" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a> <a id="21086" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21088" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a>
  <a id="21096" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="21104" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21108" class="Symbol">(</a><a id="21109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a> <a id="21111" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21113" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a><a id="21118" class="Symbol">)</a>
  <a id="21122" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="21125" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="21130" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21134" class="Symbol">(</a><a id="21135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20919" class="Function">+-suc</a> <a id="21141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a> <a id="21143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a><a id="21144" class="Symbol">)</a> <a id="21146" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="21152" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21156" class="Symbol">(</a><a id="21157" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21161" class="Symbol">(</a><a id="21162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a> <a id="21164" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a><a id="21167" class="Symbol">))</a>
  <a id="21172" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="21180" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21184" class="Symbol">(</a><a id="21185" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21061" class="Bound">m</a> <a id="21191" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21064" class="Bound">n</a><a id="21194" class="Symbol">)</a>
  <a id="21198" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:
{:/}

其签名描述了我们定义的标识符 `+-suc` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

{::comment}
Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，并返回该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + suc n ≡ suc (zero + n)

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很直白。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    suc m + suc n ≡ suc (suc m + n)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + suc n) ≡ suc (suc (m + n))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + suc n ≡ suc (m + n)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:
{:/}

从上到下或从下到上阅读等式链都会让我们在中间遇到化简后的等式。剩下的等式可由以下依据得出：

    ⟨ cong suc (+-suc m n) ⟩

{::comment}
Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.
{:/}

在这里，递归调用的 `+-suc m n` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第二条引理证毕。

{::comment}
### The proposition
{:/}

### 命题

{::comment}
Finally, here is our proposition's statement and proof:
{:/}

最后，以下是我们的命题的陈述和证明：

<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="23070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23070" class="Function">+-comm</a> <a id="23077" class="Symbol">:</a> <a id="23079" class="Symbol">∀</a> <a id="23081" class="Symbol">(</a><a id="23082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23082" class="Bound">m</a> <a id="23084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23084" class="Bound">n</a> <a id="23086" class="Symbol">:</a> <a id="23088" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="23089" class="Symbol">)</a> <a id="23091" class="Symbol">→</a> <a id="23093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23082" class="Bound">m</a> <a id="23095" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23084" class="Bound">n</a> <a id="23099" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="23101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23084" class="Bound">n</a> <a id="23103" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23082" class="Bound">m</a>
<a id="23107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23070" class="Function">+-comm</a> <a id="23114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23114" class="Bound">m</a> <a id="23116" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23121" class="Symbol">=</a>
  <a id="23125" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="23135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23114" class="Bound">m</a> <a id="23137" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23139" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="23146" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="23149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18584" class="Function">+-identityʳ</a> <a id="23161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23114" class="Bound">m</a> <a id="23163" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="23169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23114" class="Bound">m</a>
  <a id="23173" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="23181" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23186" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23114" class="Bound">m</a>
  <a id="23192" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="23194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23070" class="Function">+-comm</a> <a id="23201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a> <a id="23203" class="Symbol">(</a><a id="23204" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a><a id="23209" class="Symbol">)</a> <a id="23211" class="Symbol">=</a>
  <a id="23215" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="23225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a> <a id="23227" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23229" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a>
  <a id="23237" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="23240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20919" class="Function">+-suc</a> <a id="23246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a> <a id="23248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a> <a id="23250" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="23256" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23260" class="Symbol">(</a><a id="23261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a> <a id="23263" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a><a id="23266" class="Symbol">)</a>
  <a id="23270" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="23273" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="23278" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23282" class="Symbol">(</a><a id="23283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23070" class="Function">+-comm</a> <a id="23290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a> <a id="23292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a><a id="23293" class="Symbol">)</a> <a id="23295" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="23301" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23305" class="Symbol">(</a><a id="23306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a> <a id="23308" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a><a id="23311" class="Symbol">)</a>
  <a id="23315" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="23323" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23208" class="Bound">n</a> <a id="23329" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">m</a>
  <a id="23335" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:
{:/}

第一行描述了我们定义的标识符 `+-comm` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，并返回该等式对应实例的证据。它通过对 `n` 进行归纳来证明。（这次不是 `m`！）

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    m + zero ≡ zero + m

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    m + zero ≡ m

{::comment}
The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.
{:/}

剩下的等式可由依据 `⟨ +-identityʳ m ⟩` 得出，它调用第一条引理。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    m + suc n ≡ suc n + m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    m + suc n ≡ suc (n + m)

{::comment}
We show this in two steps.  First, we have:
{:/}

我们分两步来证明它。首先，我们有：

    m + suc n ≡ suc (m + n)

{::comment}
which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have
{:/}

它依据第二条引理 `⟨ +-suc m n ⟩` 得出。之后我们有：

    suc (m + n) ≡ suc (n + m)

{::comment}
which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.
{:/}

它依据合同性和归纳假设 `⟨ cong suc (+-comm m n) ⟩` 得出。证毕。

{::comment}
Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.
{:/}

Agda 要求标识符必须在使用前定义，因此我们必须在主命题之前展示引理，如前例所示。在实践中，我们通常会先试着证明主命题，之后所需的等式会表明需要证明的引理。


{::comment}
## Our first corollary: rearranging {#sections}
{:/}

## 第一个推论：重排定理 {#sections}

{::comment}
We can apply associativity to rearrange parentheses however we like.
Here is an example:
{:/}

我们可以随意应用结合律来重排括号。例如：

<pre class="Agda">{% raw %}<a id="+-rearrange"></a><a id="25593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25593" class="Function">+-rearrange</a> <a id="25605" class="Symbol">:</a> <a id="25607" class="Symbol">∀</a> <a id="25609" class="Symbol">(</a><a id="25610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25610" class="Bound">m</a> <a id="25612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25612" class="Bound">n</a> <a id="25614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25614" class="Bound">p</a> <a id="25616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25616" class="Bound">q</a> <a id="25618" class="Symbol">:</a> <a id="25620" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="25621" class="Symbol">)</a> <a id="25623" class="Symbol">→</a> <a id="25625" class="Symbol">(</a><a id="25626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25610" class="Bound">m</a> <a id="25628" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25612" class="Bound">n</a><a id="25631" class="Symbol">)</a> <a id="25633" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25635" class="Symbol">(</a><a id="25636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25614" class="Bound">p</a> <a id="25638" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25616" class="Bound">q</a><a id="25641" class="Symbol">)</a> <a id="25643" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="25645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25610" class="Bound">m</a> <a id="25647" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25649" class="Symbol">(</a><a id="25650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25612" class="Bound">n</a> <a id="25652" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25614" class="Bound">p</a><a id="25655" class="Symbol">)</a> <a id="25657" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25616" class="Bound">q</a>
<a id="25661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25593" class="Function">+-rearrange</a> <a id="25673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a> <a id="25679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a> <a id="25681" class="Symbol">=</a>
  <a id="25685" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="25695" class="Symbol">(</a><a id="25696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25698" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a><a id="25701" class="Symbol">)</a> <a id="25703" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25705" class="Symbol">(</a><a id="25706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a> <a id="25708" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25711" class="Symbol">)</a>
  <a id="25715" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="25718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="25726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25730" class="Symbol">(</a><a id="25731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a> <a id="25733" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25736" class="Symbol">)</a> <a id="25738" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="25744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25746" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25748" class="Symbol">(</a><a id="25749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25751" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25753" class="Symbol">(</a><a id="25754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a> <a id="25756" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25759" class="Symbol">))</a>
  <a id="25764" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="25767" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="25772" class="Symbol">(</a><a id="25773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25775" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+_</a><a id="25777" class="Symbol">)</a> <a id="25779" class="Symbol">(</a><a id="25780" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="25784" class="Symbol">(</a><a id="25785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="25793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a> <a id="25797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25798" class="Symbol">))</a> <a id="25801" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="25807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25809" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25811" class="Symbol">((</a><a id="25813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25815" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a><a id="25818" class="Symbol">)</a> <a id="25820" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25823" class="Symbol">)</a>
  <a id="25827" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="25830" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="25834" class="Symbol">(</a><a id="25835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11564" class="Function">+-assoc</a> <a id="25843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25845" class="Symbol">(</a><a id="25846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25848" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a><a id="25851" class="Symbol">)</a> <a id="25853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a><a id="25854" class="Symbol">)</a> <a id="25856" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="25862" class="Symbol">(</a><a id="25863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25673" class="Bound">m</a> <a id="25865" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25867" class="Symbol">(</a><a id="25868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25675" class="Bound">n</a> <a id="25870" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25677" class="Bound">p</a><a id="25873" class="Symbol">))</a> <a id="25876" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25679" class="Bound">q</a>
  <a id="25882" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
No induction is required, we simply apply associativity twice.
A few points are worthy of note.
{:/}

无需归纳法，我们只不过应用了两次结合律就完成了证明。其中有几点需要注意的地方。

{::comment}
First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.
{:/}

第一，加法是左结合的，因此 `m + (n + p) + q` 表示 `(m + (n + p)) + q`。

{::comment}
Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:
{:/}

第二，我们用 `sym` 来交换等式的两边。命题 `+-assoc n p q` 会将括号从右边移到左边：

    (n + p) + q ≡ n + (p + q)

{::comment}
To shift them the other way, we use `sym (+-assoc m n p)`:
{:/}

要往另一个方向移动括号，我们要用 `sym (+-assoc m n p)`：

    n + (p + q) ≡ (n + p) + q

{::comment}
In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.
{:/}

一般来说，若 `e` 提供了 `x ≡ y` 的证据，那么 `sym e` 就提供了 `y ≡ x` 的证据。

{::comment}
Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:
{:/}

第三，Agda 支持 Richard Bird 引入的**片段（section）**记法。我们将应用到
`y` 并返回 `x + y` 的函数写作 `(x +_)`。因此，应用合同性 `cong (m +_)`
会将上面的等式转换成：

    m + (n + (p + q)) ≡ m + ((n + p) + q)

{::comment}
Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.
{:/}

类似地，我们将应用到 `y` 并返回 `y + x` 的函数写作 `(_+ x)`。这同样适用于任何中缀运算符。


{::comment}
## Creation, one last time
{:/}

## 创世，最后一次

{::comment}
Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:
{:/}

我们回到结合律的证明上来，把归纳证明（或等价地，递归定义）看做一个创世故事会有助于理解。这次我们专注于判断结合律的断言：

{::comment}
     -- In the beginning, we know nothing about associativity.
{:/}

     -- 起初，我们对结合律一无所知。

{::comment}
Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:
{:/}

现在，我们将规则应用到所有已知的判断上来。起始步骤告诉我们对于所有的自然数
`n` 和 `p` 来说，`(zero + n) + p ≡ zero + (n + p)`。归纳步骤告我我们若
`(m + n) + p ≡ m + (n + p)`（在昨天）成立，那么 `(suc m + n) + p ≡ suc m + (n + p)`
（在今天）也成立。我们在今天之前并不知道任何关于结合律的判断，因此此规则并未给出任何新的判断：

{::comment}
    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
{:/}

    -- 第一天，我们知道了关于 0 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

{::comment}
Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:
{:/}

之后我们重复此过程，因此接下来一天我们知道今天以前的所有判断，以及任何通过此规则添加的判断。起始步骤并未告诉我们新的东西，而如今归归纳步骤添加了更多的判断：

{::comment}
    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
{:/}

    -- 第二天，我们知道了关于 0 和 1 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

{::comment}
And we repeat the process again:
{:/}

我们再次重复此过程：

{::comment}
    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
{:/}

    -- 第三天，我们知道了关于 0、1 和 2 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...
{:/}

    -- 第四天，我们知道了关于 0、1、2 和 3 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

{::comment}
The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.
{:/}

此过程可以继续下去。在第 **m** 天我们会知道所有第一个数小于 **m** 的判断。

{::comment}
There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.
{:/}

还有一种完全有限的方法来生成同样的等式，它的证明留作读者的练习。

{::comment}
#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}
{:/}

#### 练习 `finite-+-assoc`（延伸） {#finite-plus-assoc}

{::comment}
Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#finite-creation).
{:/}

请参考[前文]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#finite-creation)写出前四天已知的加法结合律的创世故事。

{::comment}
<pre class="Agda">{% raw %}<a id="31561" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="31614" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
## Associativity with rewrite
{:/}

## 用改写来证明结合律

{::comment}
There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{:/}

证明可不止一种方法。下面是第二种在 Agda 中证明加法结合律的方法，使用 `rewrite`（改写）
而非等式链：

<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="31945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31945" class="Function">+-assoc′</a> <a id="31954" class="Symbol">:</a> <a id="31956" class="Symbol">∀</a> <a id="31958" class="Symbol">(</a><a id="31959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31959" class="Bound">m</a> <a id="31961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31961" class="Bound">n</a> <a id="31963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31963" class="Bound">p</a> <a id="31965" class="Symbol">:</a> <a id="31967" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="31968" class="Symbol">)</a> <a id="31970" class="Symbol">→</a> <a id="31972" class="Symbol">(</a><a id="31973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31959" class="Bound">m</a> <a id="31975" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="31977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31961" class="Bound">n</a><a id="31978" class="Symbol">)</a> <a id="31980" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="31982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31963" class="Bound">p</a> <a id="31984" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="31986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31959" class="Bound">m</a> <a id="31988" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="31990" class="Symbol">(</a><a id="31991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31961" class="Bound">n</a> <a id="31993" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="31995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31963" class="Bound">p</a><a id="31996" class="Symbol">)</a>
<a id="31998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31945" class="Function">+-assoc′</a> <a id="32007" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="32015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32015" class="Bound">n</a> <a id="32017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32017" class="Bound">p</a>                          <a id="32044" class="Symbol">=</a>  <a id="32047" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="32052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31945" class="Function">+-assoc′</a> <a id="32061" class="Symbol">(</a><a id="32062" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="32066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32066" class="Bound">m</a><a id="32067" class="Symbol">)</a> <a id="32069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32069" class="Bound">n</a> <a id="32071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32071" class="Bound">p</a>  <a id="32074" class="Keyword">rewrite</a> <a id="32082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#31945" class="Function">+-assoc′</a> <a id="32091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32066" class="Bound">m</a> <a id="32093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32069" class="Bound">n</a> <a id="32095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#32071" class="Bound">p</a>  <a id="32098" class="Symbol">=</a>  <a id="32101" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    n + p ≡ n + p

{::comment}
This holds trivially. The proof that a term is equal to itself is written `refl`.
{:/}

此式平凡成立。一个项等于其自身的证明写作 `refl`（自反性）。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.
{:/}

在根据归纳假设改写后，这两项相等，其证明同样由 `refl` 给出。根据给定的等式进行改写可用关键字 `rewrite` 后跟一个该等式的证明来表示。改写不仅可以省去等式链还可以避免调用 `cong`.


{::comment}
## Commutativity with rewrite
{:/}

## 使用改写证明交换律

{::comment}
Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{:/}

下面是加法交换律的第二个证明，使用 `rewrite` 而非等式链：

<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="33419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33419" class="Function">+-identity′</a> <a id="33431" class="Symbol">:</a> <a id="33433" class="Symbol">∀</a> <a id="33435" class="Symbol">(</a><a id="33436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33436" class="Bound">n</a> <a id="33438" class="Symbol">:</a> <a id="33440" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="33441" class="Symbol">)</a> <a id="33443" class="Symbol">→</a> <a id="33445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33436" class="Bound">n</a> <a id="33447" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33449" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="33454" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="33456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33436" class="Bound">n</a>
<a id="33458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33419" class="Function">+-identity′</a> <a id="33470" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="33475" class="Symbol">=</a> <a id="33477" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="33482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33419" class="Function">+-identity′</a> <a id="33494" class="Symbol">(</a><a id="33495" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="33499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33499" class="Bound">n</a><a id="33500" class="Symbol">)</a> <a id="33502" class="Keyword">rewrite</a> <a id="33510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33419" class="Function">+-identity′</a> <a id="33522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33499" class="Bound">n</a> <a id="33524" class="Symbol">=</a> <a id="33526" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="33532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33532" class="Function">+-suc′</a> <a id="33539" class="Symbol">:</a> <a id="33541" class="Symbol">∀</a> <a id="33543" class="Symbol">(</a><a id="33544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33544" class="Bound">m</a> <a id="33546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33546" class="Bound">n</a> <a id="33548" class="Symbol">:</a> <a id="33550" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="33551" class="Symbol">)</a> <a id="33553" class="Symbol">→</a> <a id="33555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33544" class="Bound">m</a> <a id="33557" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33559" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="33563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33546" class="Bound">n</a> <a id="33565" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="33567" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="33571" class="Symbol">(</a><a id="33572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33544" class="Bound">m</a> <a id="33574" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33546" class="Bound">n</a><a id="33577" class="Symbol">)</a>
<a id="33579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33532" class="Function">+-suc′</a> <a id="33586" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="33591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33591" class="Bound">n</a> <a id="33593" class="Symbol">=</a> <a id="33595" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="33600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33532" class="Function">+-suc′</a> <a id="33607" class="Symbol">(</a><a id="33608" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="33612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33612" class="Bound">m</a><a id="33613" class="Symbol">)</a> <a id="33615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33615" class="Bound">n</a> <a id="33617" class="Keyword">rewrite</a> <a id="33625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33532" class="Function">+-suc′</a> <a id="33632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33612" class="Bound">m</a> <a id="33634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33615" class="Bound">n</a> <a id="33636" class="Symbol">=</a> <a id="33638" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="33644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33644" class="Function">+-comm′</a> <a id="33652" class="Symbol">:</a> <a id="33654" class="Symbol">∀</a> <a id="33656" class="Symbol">(</a><a id="33657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33657" class="Bound">m</a> <a id="33659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33659" class="Bound">n</a> <a id="33661" class="Symbol">:</a> <a id="33663" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="33664" class="Symbol">)</a> <a id="33666" class="Symbol">→</a> <a id="33668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33657" class="Bound">m</a> <a id="33670" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33659" class="Bound">n</a> <a id="33674" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="33676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33659" class="Bound">n</a> <a id="33678" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33657" class="Bound">m</a>
<a id="33682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33644" class="Function">+-comm′</a> <a id="33690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33690" class="Bound">m</a> <a id="33692" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="33697" class="Keyword">rewrite</a> <a id="33705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33419" class="Function">+-identity′</a> <a id="33717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33690" class="Bound">m</a> <a id="33719" class="Symbol">=</a> <a id="33721" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="33726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33644" class="Function">+-comm′</a> <a id="33734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33734" class="Bound">m</a> <a id="33736" class="Symbol">(</a><a id="33737" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="33741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33741" class="Bound">n</a><a id="33742" class="Symbol">)</a> <a id="33744" class="Keyword">rewrite</a> <a id="33752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33532" class="Function">+-suc′</a> <a id="33759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33734" class="Bound">m</a> <a id="33761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33741" class="Bound">n</a> <a id="33763" class="Symbol">|</a> <a id="33765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33644" class="Function">+-comm′</a> <a id="33773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33734" class="Bound">m</a> <a id="33775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#33741" class="Bound">n</a> <a id="33777" class="Symbol">=</a> <a id="33779" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.
{:/}

在最后一行中，用两个等式进行改写被表示为用一条竖线分隔两个相关等式的证明。左边的改写会在右边之前被执行。


{::comment}
## Building proofs interactively
{:/}

## 交互式地构造证明

{::comment}
It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:
{:/}

看看如何在 Emacs 中用 Agda 的交互式特性来构造另一种结合律的证明会很有启发性。我们从输入以下内容开始：


    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

{::comment}
The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:
{:/}

其中的问号表示你想要 Agda 帮你填充的代码。如果你按下 `C-c C-l`
（先按 Ctrl-c 再按 Ctrl-l），那么问号会被替换为：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

{::comment}
The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:
{:/}

空的大括号叫做**洞（Hole）**，0 是用来指代此洞的编号。洞可能会以绿色高亮显示。
Emacs 还会在屏幕下方创建一个新的窗口并显示文本：

    ?0 : ((m + n) + p) ≡ (m + (n + p))

{::comment}
This indicates that hole 0 is to be filled in with a proof of
the stated judgment.
{:/}

这表示 0 号洞需要以所提示的判断的证明来填充。

{::comment}
We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:
{:/}

我们希望通过对 `m` 进行归纳来证明此命题。将光标移动到洞中并按下
`C-c C-c`。它会给出提示：

    pattern variables to case (empty for split on result):

{::comment}
Typing `m` will cause a split on that variable, resulting
in an update to the code:
{:/}

按下 `m` 会拆分该变量，并更新此代码：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

{::comment}
There are now two holes, and the window at the bottom tells you what
each is required to prove:
{:/}

现在有两个洞了，下方的窗口会告诉你每个洞中需要证明的内容：

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

{::comment}
Going into hole 0 and typing `C-c C-,` will display the text:
{:/}

进入 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

{::comment}
This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:
{:/}

它表示在化简之后，0 号洞的目标如上所示，所示类型的变量 `p` 和 `n` 可在证明中使用。给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充。按下 `C-c C-l`
会将剩下的洞重新编号为 0：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

{::comment}
Going into the new hole 0 and typing `C-c C-,` will display the text:
{:/}

进入新的 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:
{:/}

同样，它会给出化简后的目标和可用的变量。在此步骤中，我们需要根据归纳假设进行改写，于是我来编辑这些文本：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

{::comment}
Going into the remaining hole and typing `C-c C-,` will display the text:
{:/}

进入剩下的洞中并按下 `C-c C-,` 会显示以下文本：

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:
{:/}

给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充并完成证明：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


{::comment}
#### Exercise `+-swap` (recommended) {#plus-swap}
{:/}

#### 练习：`+-swap`（推荐） {#plus-swap}

{::comment}
Show
{:/}

请证明对于所有的自然数 `m`、`n` 和 `p`，

    m + (n + p) ≡ n + (m + p)

{::comment}
for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.
{:/}

成立。无需归纳证明，只需应用前面满足结合律和交换律的结果即可。

<pre class="Agda">{% raw %}<a id="38457" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="38510" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}
{:/}

#### 练习 `*-distrib-+`（推荐） {#times-distrib-plus}

{::comment}
Show multiplication distributes over addition, that is,
{:/}

请证明乘法对加法满足分配律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m + n) * p ≡ m * p + n * p

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
<pre class="Agda">{% raw %}<a id="38897" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="38950" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `*-assoc` (recommended) {#times-assoc}
{:/}

#### 练习 `*-assoc`（推荐） {#times-assoc}

{::comment}
Show multiplication is associative, that is,
{:/}

请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m * n) * p ≡ m * (n * p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
<pre class="Agda">{% raw %}<a id="39299" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="39352" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `*-comm` {#times-comm}
{:/}

#### 练习 `*-comm` {#times-comm}

{::comment}
Show multiplication is commutative, that is,
{:/}

请证明乘法满足交换律，即对于所有的自然数 `m` 和 `n`，

    m * n ≡ n * m

{::comment}
for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.
{:/}

成立。和加法交换律一样，你需要陈述并证明配套的引理。

{::comment}
<pre class="Agda">{% raw %}<a id="39770" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="39823" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `0∸n≡0` {#zero-monus}
{:/}

#### 练习 `0∸n≡0` {#zero-monus}

{::comment}
Show
{:/}

请证明对于所有的自然数 `n`，

    zero ∸ n ≡ zero

{::comment}
for all naturals `n`. Did your proof require induction?
{:/}

成立。你的证明需要归纳法吗？

{::comment}
<pre class="Agda">{% raw %}<a id="40111" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="40164" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `∸-+-assoc` {#monus-plus-assoc}
{:/}

#### 练习 `∸-+-assoc` {#monus-plus-assoc}

{::comment}
Show that monus associates with addition, that is,
{:/}

请证明饱和减法与加法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    m ∸ n ∸ p ≡ m ∸ (n + p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
<pre class="Agda">{% raw %}<a id="40519" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="40572" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `+*^` (stretch)
{:/}

#### 练习 `+*^` （延伸）

{::comment}
Show the following three laws
{:/}

证明下列三条定律

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

{::comment}
for all `m`, `n`, and `p`.
{:/}

对于所有 `m`、`n` 和 `p` 成立。


#### Exercise `Bin-laws` (stretch) {#Bin-laws}
{:/}

#### 练习 `Bin-laws`（延伸） {#Bin-laws}

{::comment}
Recall that
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype of bitstrings representing natural numbers
{:/}

回想练习 [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) 中定义了一种比特串数据类型来表示自然数

<pre class="Agda">{% raw %}<a id="41176" class="Keyword">data</a> <a id="Bin"></a><a id="41181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a> <a id="41185" class="Symbol">:</a> <a id="41187" class="PrimitiveType">Set</a> <a id="41191" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="41199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41199" class="InductiveConstructor">nil</a> <a id="41203" class="Symbol">:</a> <a id="41205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="41211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41211" class="InductiveConstructor Operator">x0_</a> <a id="41215" class="Symbol">:</a> <a id="41217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a> <a id="41221" class="Symbol">→</a> <a id="41223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="41229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41229" class="InductiveConstructor Operator">x1_</a> <a id="41233" class="Symbol">:</a> <a id="41235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a> <a id="41239" class="Symbol">→</a> <a id="41241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#41181" class="Datatype">Bin</a>{% endraw %}</pre>

{::comment}
and asks you to define functions
{:/}

并要求你定义函数

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

{::comment}
Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:
{:/}

考虑以下定律，其中 `n` 表示自然数，`x` 表示比特串：

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

{::comment}
For each law: if it holds, prove; if not, give a counterexample.
{:/}

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

{::comment}
<pre class="Agda">{% raw %}<a id="41729" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="41782" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中类似的定义可在标准库中找到：

<pre class="Agda">{% raw %}<a id="41987" class="Keyword">import</a> <a id="41994" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="42014" class="Keyword">using</a> <a id="42020" class="Symbol">(</a><a id="42021" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9375" class="Function">+-assoc</a><a id="42028" class="Symbol">;</a> <a id="42030" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9531" class="Function">+-identityʳ</a><a id="42041" class="Symbol">;</a> <a id="42043" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9272" class="Function">+-suc</a><a id="42048" class="Symbol">;</a> <a id="42050" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="42056" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
## Unicode
{:/}

## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

本章中使用了以下 Unicode：

{::comment}
    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')
{:/}

    ∀  U+2200  对于所有 (\forall, \all)
    ʳ  U+02B3  小写字母 r 的变体 (\^r)
    ′  U+2032  撇号 (\')
    ″  U+2033  双撇号 (\')
    ‴  U+2034  三撇号 (\')
    ⁗  U+2057  四撇号 (\')

{::comment}
Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
{:/}

与 `\r` 类似，命令 `\^r` 列出了多种上标右箭头的变体，以及上标的字母 `r`。命令 `\'` 列出了一些撇号（`′ ″ ‴ ⁗`）。
