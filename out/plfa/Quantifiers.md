---
src       : src/plfa/Quantifiers.lagda
title     : "Quantifiers: 全称量词与存在量词"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
translators: ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="195" class="Keyword">module</a> <a id="202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}" class="Module">plfa.Quantifiers</a> <a id="219" class="Keyword">where</a>{% endraw %}</pre>

{::comment}
This chapter introduces universal and existential quantification.
{:/}

本章节介绍全称量化（Universal Quantification）和存在量化（Existential Quantification）。

{::comment}
## Imports
{:/}

## 导入

<pre class="Agda">{% raw %}<a id="441" class="Keyword">import</a> <a id="448" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="486" class="Symbol">as</a> <a id="489" class="Module">Eq</a>
<a id="492" class="Keyword">open</a> <a id="497" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="500" class="Keyword">using</a> <a id="506" class="Symbol">(</a><a id="507" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="510" class="Symbol">;</a> <a id="512" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="516" class="Symbol">)</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="539" class="Keyword">using</a> <a id="545" class="Symbol">(</a><a id="546" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="547" class="Symbol">;</a> <a id="549" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="553" class="Symbol">;</a> <a id="555" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="558" class="Symbol">;</a> <a id="560" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="563" class="Symbol">;</a> <a id="565" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="568" class="Symbol">)</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="599" class="Keyword">using</a> <a id="605" class="Symbol">(</a><a id="606" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="608" class="Symbol">)</a>
<a id="610" class="Keyword">open</a> <a id="615" class="Keyword">import</a> <a id="622" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html" class="Module">Data.Product</a> <a id="635" class="Keyword">using</a> <a id="641" class="Symbol">(</a><a id="642" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">_×_</a><a id="645" class="Symbol">;</a> <a id="647" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#155" class="Field">proj₁</a><a id="652" class="Symbol">)</a> <a id="654" class="Keyword">renaming</a> <a id="663" class="Symbol">(</a><a id="664" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">_,_</a> <a id="668" class="Symbol">to</a> <a id="671" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="676" class="Symbol">)</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.html" class="Module">Data.Sum</a> <a id="699" class="Keyword">using</a> <a id="705" class="Symbol">(</a><a id="706" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.Base.html#419" class="Datatype Operator">_⊎_</a><a id="709" class="Symbol">)</a>
<a id="711" class="Keyword">open</a> <a id="716" class="Keyword">import</a> <a id="723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="740" class="Keyword">using</a> <a id="746" class="Symbol">(</a><a id="747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">_≃_</a><a id="750" class="Symbol">;</a> <a id="752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a><a id="766" class="Symbol">)</a>{% endraw %}</pre>


{::comment}
## Universals
{:/}

## 全称量化

{::comment}
We formalise universal quantification using the
dependent function type, which has appeared throughout this book.
{:/}

我们用依赖函数类型（Dependent Function Type）来形式化全称量化。这样的形式贯穿全书地出现。


{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

{::comment}
Evidence that `∀ (x : A) → B x` holds is of the form
{:/}

`∀ (x : A) → B x` 成立的证明由以下形式构成：

    λ (x : A) → N x

{::comment}
where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.
{:/}

其中 `N x` 是一个 `B x` 类型的项，`N x` 和 `B x` 都包含了一个 `A` 类型的自由变量 `x`。给定一个项 `L`， 其提供 `∀ (x : A) → B x` 成立的证明，和一个类型为 `A` 的项 `M`，
`L M` 这一项则是 `B M` 成立的证明。换句话说，`∀ (x : A) → B x` 成立的证明是一个函数，将类型为 `A` 的项 `M` 转换成 `B M` 成立的证明。

{::comment}
Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{:/}

再换句话说，如果我们知道 `∀ (x : A) → B x` 成立，又知道 `M` 是一个类型为 `A` 的项，那么我们可以推导出 `B M` 成立：
<pre class="Agda">{% raw %}<a id="∀-elim"></a><a id="2610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2610" class="Function">∀-elim</a> <a id="2617" class="Symbol">:</a> <a id="2619" class="Symbol">∀</a> <a id="2621" class="Symbol">{</a><a id="2622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2622" class="Bound">A</a> <a id="2624" class="Symbol">:</a> <a id="2626" class="PrimitiveType">Set</a><a id="2629" class="Symbol">}</a> <a id="2631" class="Symbol">{</a><a id="2632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2632" class="Bound">B</a> <a id="2634" class="Symbol">:</a> <a id="2636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2622" class="Bound">A</a> <a id="2638" class="Symbol">→</a> <a id="2640" class="PrimitiveType">Set</a><a id="2643" class="Symbol">}</a>
  <a id="2647" class="Symbol">→</a> <a id="2649" class="Symbol">(</a><a id="2650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2650" class="Bound">L</a> <a id="2652" class="Symbol">:</a> <a id="2654" class="Symbol">∀</a> <a id="2656" class="Symbol">(</a><a id="2657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2657" class="Bound">x</a> <a id="2659" class="Symbol">:</a> <a id="2661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2622" class="Bound">A</a><a id="2662" class="Symbol">)</a> <a id="2664" class="Symbol">→</a> <a id="2666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2632" class="Bound">B</a> <a id="2668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2657" class="Bound">x</a><a id="2669" class="Symbol">)</a>
  <a id="2673" class="Symbol">→</a> <a id="2675" class="Symbol">(</a><a id="2676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2676" class="Bound">M</a> <a id="2678" class="Symbol">:</a> <a id="2680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2622" class="Bound">A</a><a id="2681" class="Symbol">)</a>
    <a id="2687" class="Comment">-----------------</a>
  <a id="2707" class="Symbol">→</a> <a id="2709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2632" class="Bound">B</a> <a id="2711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2676" class="Bound">M</a>
<a id="2713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2610" class="Function">∀-elim</a> <a id="2720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2720" class="Bound">L</a> <a id="2722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2722" class="Bound">M</a> <a id="2724" class="Symbol">=</a> <a id="2726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2720" class="Bound">L</a> <a id="2728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2722" class="Bound">M</a>{% endraw %}</pre>
{::comment}
As with `→-elim`, the rule corresponds to function application.
{:/}

如 `→-elim` 那样，这条规则对应了函数应用。

{::comment}
Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.
{:/}

函数是依赖函数的一种特殊形式，其值域不取决于定义域中的变量。当一个函数被视为蕴含的证明时，它的参数和结果都是证明，而当一个依赖函数被视为全称量词的证明时，它的参数被视为数据类型中的一个元素，而结果是一个依赖于参数的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上取决于如何来诠释。

{::comment}
Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.
{:/}

依赖函数类型也被叫做依赖积（Dependent Product），因为如果 `A` 是一个有限的数据类型，有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，那么 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。的确，`∀ (x : A) → B x` 的记法有时也被 `Π[ x ∈ A ] (B x)` 取代，其中 `Π` 代表积。然而，我们还是使用依赖函数这个名称，因为依赖积这个名称是有歧义的，我们后续会体会到歧义所在。

{::comment}
#### Exercise `∀-distrib-×` (recommended)
{:/}

#### 练习 `∀-distrib-×` （推荐）

{::comment}
Show that universals distribute over conjunction:
{:/}

证明全程量词对于合取满足分配律：

<pre class="Agda">{% raw %}<a id="4613" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="4625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4625" class="Postulate">∀-distrib-×</a> <a id="4637" class="Symbol">:</a> <a id="4639" class="Symbol">∀</a> <a id="4641" class="Symbol">{</a><a id="4642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4642" class="Bound">A</a> <a id="4644" class="Symbol">:</a> <a id="4646" class="PrimitiveType">Set</a><a id="4649" class="Symbol">}</a> <a id="4651" class="Symbol">{</a><a id="4652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4652" class="Bound">B</a> <a id="4654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4654" class="Bound">C</a> <a id="4656" class="Symbol">:</a> <a id="4658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4642" class="Bound">A</a> <a id="4660" class="Symbol">→</a> <a id="4662" class="PrimitiveType">Set</a><a id="4665" class="Symbol">}</a> <a id="4667" class="Symbol">→</a>
    <a id="4673" class="Symbol">(∀</a> <a id="4676" class="Symbol">(</a><a id="4677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4677" class="Bound">x</a> <a id="4679" class="Symbol">:</a> <a id="4681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4642" class="Bound">A</a><a id="4682" class="Symbol">)</a> <a id="4684" class="Symbol">→</a> <a id="4686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4652" class="Bound">B</a> <a id="4688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4677" class="Bound">x</a> <a id="4690" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">×</a> <a id="4692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4654" class="Bound">C</a> <a id="4694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4677" class="Bound">x</a><a id="4695" class="Symbol">)</a> <a id="4697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="4699" class="Symbol">(∀</a> <a id="4702" class="Symbol">(</a><a id="4703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4703" class="Bound">x</a> <a id="4705" class="Symbol">:</a> <a id="4707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4642" class="Bound">A</a><a id="4708" class="Symbol">)</a> <a id="4710" class="Symbol">→</a> <a id="4712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4652" class="Bound">B</a> <a id="4714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4703" class="Bound">x</a><a id="4715" class="Symbol">)</a> <a id="4717" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">×</a> <a id="4719" class="Symbol">(∀</a> <a id="4722" class="Symbol">(</a><a id="4723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4723" class="Bound">x</a> <a id="4725" class="Symbol">:</a> <a id="4727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4642" class="Bound">A</a><a id="4728" class="Symbol">)</a> <a id="4730" class="Symbol">→</a> <a id="4732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4654" class="Bound">C</a> <a id="4734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4723" class="Bound">x</a><a id="4735" class="Symbol">)</a>{% endraw %}</pre>
{::comment}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).
{:/

将这个结果与 [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}) 章节中的 (`→-distrib-×`) 结果对比。

{::comment}
#### Exercise `⊎∀-implies-∀⊎`
{:/}

#### 练习 `⊎∀-implies-∀⊎`

{::comment}
Show that a disjunction of universals implies a universal of disjunctions:
{:/}

证明全称量词的析取蕴含了析取的全称量词：

<pre class="Agda">{% raw %}<a id="5122" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="5134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5134" class="Postulate">⊎∀-implies-∀⊎</a> <a id="5148" class="Symbol">:</a> <a id="5150" class="Symbol">∀</a> <a id="5152" class="Symbol">{</a><a id="5153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5153" class="Bound">A</a> <a id="5155" class="Symbol">:</a> <a id="5157" class="PrimitiveType">Set</a><a id="5160" class="Symbol">}</a> <a id="5162" class="Symbol">{</a><a id="5163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5163" class="Bound">B</a> <a id="5165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5165" class="Bound">C</a> <a id="5167" class="Symbol">:</a> <a id="5169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5153" class="Bound">A</a> <a id="5171" class="Symbol">→</a> <a id="5173" class="PrimitiveType">Set</a><a id="5176" class="Symbol">}</a> <a id="5178" class="Symbol">→</a>
    <a id="5184" class="Symbol">(∀</a> <a id="5187" class="Symbol">(</a><a id="5188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5188" class="Bound">x</a> <a id="5190" class="Symbol">:</a> <a id="5192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5153" class="Bound">A</a><a id="5193" class="Symbol">)</a> <a id="5195" class="Symbol">→</a> <a id="5197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5163" class="Bound">B</a> <a id="5199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5188" class="Bound">x</a><a id="5200" class="Symbol">)</a> <a id="5202" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="5204" class="Symbol">(∀</a> <a id="5207" class="Symbol">(</a><a id="5208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5208" class="Bound">x</a> <a id="5210" class="Symbol">:</a> <a id="5212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5153" class="Bound">A</a><a id="5213" class="Symbol">)</a> <a id="5215" class="Symbol">→</a> <a id="5217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5165" class="Bound">C</a> <a id="5219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5208" class="Bound">x</a><a id="5220" class="Symbol">)</a>  <a id="5223" class="Symbol">→</a>  <a id="5226" class="Symbol">∀</a> <a id="5228" class="Symbol">(</a><a id="5229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5229" class="Bound">x</a> <a id="5231" class="Symbol">:</a> <a id="5233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5153" class="Bound">A</a><a id="5234" class="Symbol">)</a> <a id="5236" class="Symbol">→</a> <a id="5238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5163" class="Bound">B</a> <a id="5240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5229" class="Bound">x</a> <a id="5242" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="5244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5165" class="Bound">C</a> <a id="5246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5229" class="Bound">x</a>{% endraw %}</pre>
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

反命题成立么？如果成立，给出证明。如果不成立，解释为什么。


{::comment}
#### Exercise `∀-×`
{:/}

#### 练习 `∀-×`

{::comment}
Consider the following type.
{:/}

参考下面的类型：

<pre class="Agda">{% raw %}<a id="5491" class="Keyword">data</a> <a id="Tri"></a><a id="5496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5496" class="Datatype">Tri</a> <a id="5500" class="Symbol">:</a> <a id="5502" class="PrimitiveType">Set</a> <a id="5506" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="5514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5514" class="InductiveConstructor">aa</a> <a id="5517" class="Symbol">:</a> <a id="5519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5496" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="5525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5525" class="InductiveConstructor">bb</a> <a id="5528" class="Symbol">:</a> <a id="5530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5496" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="5536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5536" class="InductiveConstructor">cc</a> <a id="5539" class="Symbol">:</a> <a id="5541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5496" class="Datatype">Tri</a>{% endraw %}</pre>
{::comment}
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。


{::comment}
## Existentials
{:/}

## 存在量化

{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，存在量化的命题 `Σ[ x ∈ A ] B x` 当对于一些类型为 `A` 的项 `M`，命题 `B M` 成立时成立。在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

{::comment}
We formalise existential quantification by declaring a suitable
inductive type:
{:/}

我们定义一个合适的归纳数据类型来形式化存在量化：

<pre class="Agda">{% raw %}<a id="6595" class="Keyword">data</a> <a id="Σ"></a><a id="6600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6600" class="Datatype">Σ</a> <a id="6602" class="Symbol">(</a><a id="6603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6603" class="Bound">A</a> <a id="6605" class="Symbol">:</a> <a id="6607" class="PrimitiveType">Set</a><a id="6610" class="Symbol">)</a> <a id="6612" class="Symbol">(</a><a id="6613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6613" class="Bound">B</a> <a id="6615" class="Symbol">:</a> <a id="6617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6603" class="Bound">A</a> <a id="6619" class="Symbol">→</a> <a id="6621" class="PrimitiveType">Set</a><a id="6624" class="Symbol">)</a> <a id="6626" class="Symbol">:</a> <a id="6628" class="PrimitiveType">Set</a> <a id="6632" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="6640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="6646" class="Symbol">:</a> <a id="6648" class="Symbol">(</a><a id="6649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6649" class="Bound">x</a> <a id="6651" class="Symbol">:</a> <a id="6653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6603" class="Bound">A</a><a id="6654" class="Symbol">)</a> <a id="6656" class="Symbol">→</a> <a id="6658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6613" class="Bound">B</a> <a id="6660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6649" class="Bound">x</a> <a id="6662" class="Symbol">→</a> <a id="6664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6600" class="Datatype">Σ</a> <a id="6666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6603" class="Bound">A</a> <a id="6668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6613" class="Bound">B</a>{% endraw %}</pre>
{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

<pre class="Agda">{% raw %}<a id="Σ-syntax"></a><a id="6790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6790" class="Function">Σ-syntax</a> <a id="6799" class="Symbol">=</a> <a id="6801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6600" class="Datatype">Σ</a>
<a id="6803" class="Keyword">infix</a> <a id="6809" class="Number">2</a> <a id="6811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6790" class="Function">Σ-syntax</a>
<a id="6820" class="Keyword">syntax</a> <a id="6827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6790" class="Function">Σ-syntax</a> A <a id="6838" class="Symbol">(λ</a> x <a id="6843" class="Symbol">→</a> B<a id="6846" class="Symbol">)</a> <a id="6848" class="Symbol">=</a> Σ[ x ∈ A ] B{% endraw %}</pre>
{::comment}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.
{:/}

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

{::comment}
Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.
{:/}

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M` 是类型为 `A` 的项，
`N` 是 `B M` 成立的证明。


{::comment}
Equivalently, we could also declare existentials as a record type:
{:/}

我们也可以用记录类型来等价地定义存在量化。

<pre class="Agda">{% raw %}<a id="7530" class="Keyword">record</a> <a id="Σ′"></a><a id="7537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7537" class="Record">Σ′</a> <a id="7540" class="Symbol">(</a><a id="7541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7541" class="Bound">A</a> <a id="7543" class="Symbol">:</a> <a id="7545" class="PrimitiveType">Set</a><a id="7548" class="Symbol">)</a> <a id="7550" class="Symbol">(</a><a id="7551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7551" class="Bound">B</a> <a id="7553" class="Symbol">:</a> <a id="7555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7541" class="Bound">A</a> <a id="7557" class="Symbol">→</a> <a id="7559" class="PrimitiveType">Set</a><a id="7562" class="Symbol">)</a> <a id="7564" class="Symbol">:</a> <a id="7566" class="PrimitiveType">Set</a> <a id="7570" class="Keyword">where</a>
  <a id="7578" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="7588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7588" class="Field">proj₁′</a> <a id="7595" class="Symbol">:</a> <a id="7597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7541" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="7603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7603" class="Field">proj₂′</a> <a id="7610" class="Symbol">:</a> <a id="7612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7551" class="Bound">B</a> <a id="7614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7588" class="Field">proj₁′</a>{% endraw %}</pre>

{::comment}
Here record construction
{:/}

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应了项

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B M`.
{:/}

其中 `M` 是类型为 `A` 的项，`N` 是类型为 `B M` 的项。

{::comment}
Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.
{:/}

积是依赖积的一种特殊形式，其第二分量不取决于第一分量中的变量。当一个积被视为合取的证明时，它的两个分量都是证明，而当一个依赖积被视为存在量词的证明时，它的第一分量被视为数据类型中的一个元素，而第二分量是一个依赖于第一分量的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上取决于如何来诠释。

{::comment}
Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.
{:/}

存在量化也被叫做依赖和（Dependent Sum），因为如果 `A` 是一个有限的数据类型，有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，那么 `Σ[ x ∈ A ] B x` 有 `m₁ + ⋯ + mₙ` 个成员，这也解释了选择使用这个记法的原因——
`Σ` 代表和。

{::comment}
Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.
{:/}

存在量化有时也被叫做依赖积（Dependent Product），因为积是其中的一种特殊形式。但是，这样的叫法非常让人困扰，因为全程量化也被叫做依赖积，而存在量化已经有依赖和的叫法。

{::comment}
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{:/}

存在量词的普通记法是 `∃` （与全程量词的 `∀` 记法相类似）。我们使用 Agda 标准库中的惯例，使用一种隐式申明约束变量定义域的记法。

<pre class="Agda">{% raw %}<a id="∃"></a><a id="9980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9980" class="Function">∃</a> <a id="9982" class="Symbol">:</a> <a id="9984" class="Symbol">∀</a> <a id="9986" class="Symbol">{</a><a id="9987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9987" class="Bound">A</a> <a id="9989" class="Symbol">:</a> <a id="9991" class="PrimitiveType">Set</a><a id="9994" class="Symbol">}</a> <a id="9996" class="Symbol">(</a><a id="9997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9997" class="Bound">B</a> <a id="9999" class="Symbol">:</a> <a id="10001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9987" class="Bound">A</a> <a id="10003" class="Symbol">→</a> <a id="10005" class="PrimitiveType">Set</a><a id="10008" class="Symbol">)</a> <a id="10010" class="Symbol">→</a> <a id="10012" class="PrimitiveType">Set</a>
<a id="10016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9980" class="Function">∃</a> <a id="10018" class="Symbol">{</a><a id="10019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10019" class="Bound">A</a><a id="10020" class="Symbol">}</a> <a id="10022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10022" class="Bound">B</a> <a id="10024" class="Symbol">=</a> <a id="10026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6600" class="Datatype">Σ</a> <a id="10028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10019" class="Bound">A</a> <a id="10030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10022" class="Bound">B</a>

<a id="∃-syntax"></a><a id="10033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃-syntax</a> <a id="10042" class="Symbol">=</a> <a id="10044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9980" class="Function">∃</a>
<a id="10046" class="Keyword">syntax</a> <a id="10053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃-syntax</a> <a id="10062" class="Symbol">(λ</a> x <a id="10067" class="Symbol">→</a> B<a id="10070" class="Symbol">)</a> <a id="10072" class="Symbol">=</a> ∃[ x ] B{% endraw %}</pre>
{::comment}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.
{:/}

这种特殊的语法只有在 `∃-syntax` 标识符被导入时可用。我们将倾向于使用这种语法，因为它更短，而且看上去更熟悉。

{::comment}
Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{:/}

给定 `∀ x → B x → C` 成立的证明，其中 `C` 不包括自由变量 `x`，给定 `∃[ x ] B x` 成立的证明，我们可以推导出 `C` 成立。

<pre class="Agda">{% raw %}<a id="∃-elim"></a><a id="10613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10613" class="Function">∃-elim</a> <a id="10620" class="Symbol">:</a> <a id="10622" class="Symbol">∀</a> <a id="10624" class="Symbol">{</a><a id="10625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10625" class="Bound">A</a> <a id="10627" class="Symbol">:</a> <a id="10629" class="PrimitiveType">Set</a><a id="10632" class="Symbol">}</a> <a id="10634" class="Symbol">{</a><a id="10635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10635" class="Bound">B</a> <a id="10637" class="Symbol">:</a> <a id="10639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10625" class="Bound">A</a> <a id="10641" class="Symbol">→</a> <a id="10643" class="PrimitiveType">Set</a><a id="10646" class="Symbol">}</a> <a id="10648" class="Symbol">{</a><a id="10649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10649" class="Bound">C</a> <a id="10651" class="Symbol">:</a> <a id="10653" class="PrimitiveType">Set</a><a id="10656" class="Symbol">}</a>
  <a id="10660" class="Symbol">→</a> <a id="10662" class="Symbol">(∀</a> <a id="10665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10665" class="Bound">x</a> <a id="10667" class="Symbol">→</a> <a id="10669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10635" class="Bound">B</a> <a id="10671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10665" class="Bound">x</a> <a id="10673" class="Symbol">→</a> <a id="10675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10649" class="Bound">C</a><a id="10676" class="Symbol">)</a>
  <a id="10680" class="Symbol">→</a> <a id="10682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="10685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10685" class="Bound">x</a> <a id="10687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="10689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10635" class="Bound">B</a> <a id="10691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10685" class="Bound">x</a>
    <a id="10697" class="Comment">---------------</a>
  <a id="10715" class="Symbol">→</a> <a id="10717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10649" class="Bound">C</a>
<a id="10719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10613" class="Function">∃-elim</a> <a id="10726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10726" class="Bound">f</a> <a id="10728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="10730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10730" class="Bound">x</a> <a id="10732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="10734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10734" class="Bound">y</a> <a id="10736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="10738" class="Symbol">=</a> <a id="10740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10726" class="Bound">f</a> <a id="10742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10730" class="Bound">x</a> <a id="10744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10734" class="Bound">y</a>{% endraw %}</pre>
{::comment}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.
{:/}

换句话说，如果我们知道对于任何 `A` 类型的 `x`，`B x` 蕴含了 `C`，还知道对于某个类型
`A` 的 `x`，`B x` 成立，那么我们可以推导出 `C` 成立。这是因为我们可以先将 `∀ x → B x → C`
的证明对于 `A` 类型的 `x` 和 `B x` 类型的 `y` 实例化，而这样的值恰好可以由 `∃[ x ] B x`
的证明来提供。

{::comment}
Indeed, the converse also holds, and the two together form an isomorphism:
{:/}

的确，反命题也成立，两者合起来构成一个同构：

<pre class="Agda">{% raw %}<a id="∀∃-currying"></a><a id="11455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11455" class="Function">∀∃-currying</a> <a id="11467" class="Symbol">:</a> <a id="11469" class="Symbol">∀</a> <a id="11471" class="Symbol">{</a><a id="11472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11472" class="Bound">A</a> <a id="11474" class="Symbol">:</a> <a id="11476" class="PrimitiveType">Set</a><a id="11479" class="Symbol">}</a> <a id="11481" class="Symbol">{</a><a id="11482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11482" class="Bound">B</a> <a id="11484" class="Symbol">:</a> <a id="11486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11472" class="Bound">A</a> <a id="11488" class="Symbol">→</a> <a id="11490" class="PrimitiveType">Set</a><a id="11493" class="Symbol">}</a> <a id="11495" class="Symbol">{</a><a id="11496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11496" class="Bound">C</a> <a id="11498" class="Symbol">:</a> <a id="11500" class="PrimitiveType">Set</a><a id="11503" class="Symbol">}</a>
  <a id="11507" class="Symbol">→</a> <a id="11509" class="Symbol">(∀</a> <a id="11512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11512" class="Bound">x</a> <a id="11514" class="Symbol">→</a> <a id="11516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11482" class="Bound">B</a> <a id="11518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11512" class="Bound">x</a> <a id="11520" class="Symbol">→</a> <a id="11522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11496" class="Bound">C</a><a id="11523" class="Symbol">)</a> <a id="11525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="11527" class="Symbol">(</a><a id="11528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="11531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11531" class="Bound">x</a> <a id="11533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="11535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11482" class="Bound">B</a> <a id="11537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11531" class="Bound">x</a> <a id="11539" class="Symbol">→</a> <a id="11541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11496" class="Bound">C</a><a id="11542" class="Symbol">)</a>
<a id="11544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11455" class="Function">∀∃-currying</a> <a id="11556" class="Symbol">=</a>
  <a id="11560" class="Keyword">record</a>
    <a id="11571" class="Symbol">{</a> <a id="11573" class="Field">to</a>      <a id="11581" class="Symbol">=</a>  <a id="11584" class="Symbol">λ{</a> <a id="11587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11587" class="Bound">f</a> <a id="11589" class="Symbol">→</a> <a id="11591" class="Symbol">λ{</a> <a id="11594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="11596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11596" class="Bound">x</a> <a id="11598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="11600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11600" class="Bound">y</a> <a id="11602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="11604" class="Symbol">→</a> <a id="11606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11587" class="Bound">f</a> <a id="11608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11596" class="Bound">x</a> <a id="11610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11600" class="Bound">y</a> <a id="11612" class="Symbol">}}</a>
    <a id="11619" class="Symbol">;</a> <a id="11621" class="Field">from</a>    <a id="11629" class="Symbol">=</a>  <a id="11632" class="Symbol">λ{</a> <a id="11635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11635" class="Bound">g</a> <a id="11637" class="Symbol">→</a> <a id="11639" class="Symbol">λ{</a> <a id="11642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11642" class="Bound">x</a> <a id="11644" class="Symbol">→</a> <a id="11646" class="Symbol">λ{</a> <a id="11649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11649" class="Bound">y</a> <a id="11651" class="Symbol">→</a> <a id="11653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11635" class="Bound">g</a> <a id="11655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="11657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11642" class="Bound">x</a> <a id="11659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="11661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11649" class="Bound">y</a> <a id="11663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="11665" class="Symbol">}}}</a>
    <a id="11673" class="Symbol">;</a> <a id="11675" class="Field">from∘to</a> <a id="11683" class="Symbol">=</a>  <a id="11686" class="Symbol">λ{</a> <a id="11689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11689" class="Bound">f</a> <a id="11691" class="Symbol">→</a> <a id="11693" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="11698" class="Symbol">}</a>
    <a id="11704" class="Symbol">;</a> <a id="11706" class="Field">to∘from</a> <a id="11714" class="Symbol">=</a>  <a id="11717" class="Symbol">λ{</a> <a id="11720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11720" class="Bound">g</a> <a id="11722" class="Symbol">→</a> <a id="11724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a> <a id="11739" class="Symbol">λ{</a> <a id="11742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="11744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11744" class="Bound">x</a> <a id="11746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="11748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11748" class="Bound">y</a> <a id="11750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="11752" class="Symbol">→</a> <a id="11754" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="11759" class="Symbol">}}</a>
    <a id="11766" class="Symbol">}</a>{% endraw %}</pre>
{::comment}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}{% link out/plfa/Connectives.md%}#implication).
{:/}

这可以被看做是将柯里化推广的结果。的确，建立这两者同构的证明与之前我们讨论
[蕴含]({{ site.baseurl }}{% link out/plfa/Connectives.md%}#implication)时给出的证明是一样的。

{::comment}
#### Exercise `∃-distrib-⊎` (recommended)
{:/}

#### 练习 `∃-distrib-⊎` （推荐）

{::comment}
Show that existentials distribute over disjunction:
{:/}

证明存在量词对于析取满足分配律：

<pre class="Agda">{% raw %}<a id="12267" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="12279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12279" class="Postulate">∃-distrib-⊎</a> <a id="12291" class="Symbol">:</a> <a id="12293" class="Symbol">∀</a> <a id="12295" class="Symbol">{</a><a id="12296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12296" class="Bound">A</a> <a id="12298" class="Symbol">:</a> <a id="12300" class="PrimitiveType">Set</a><a id="12303" class="Symbol">}</a> <a id="12305" class="Symbol">{</a><a id="12306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12306" class="Bound">B</a> <a id="12308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12308" class="Bound">C</a> <a id="12310" class="Symbol">:</a> <a id="12312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12296" class="Bound">A</a> <a id="12314" class="Symbol">→</a> <a id="12316" class="PrimitiveType">Set</a><a id="12319" class="Symbol">}</a> <a id="12321" class="Symbol">→</a>
    <a id="12327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12330" class="Bound">x</a> <a id="12332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12334" class="Symbol">(</a><a id="12335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12306" class="Bound">B</a> <a id="12337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12330" class="Bound">x</a> <a id="12339" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="12341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12308" class="Bound">C</a> <a id="12343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12330" class="Bound">x</a><a id="12344" class="Symbol">)</a> <a id="12346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="12348" class="Symbol">(</a><a id="12349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12352" class="Bound">x</a> <a id="12354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12306" class="Bound">B</a> <a id="12358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12352" class="Bound">x</a><a id="12359" class="Symbol">)</a> <a id="12361" href="https://agda.github.io/agda-stdlib/v0.17/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="12363" class="Symbol">(</a><a id="12364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12367" class="Bound">x</a> <a id="12369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12308" class="Bound">C</a> <a id="12373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12367" class="Bound">x</a><a id="12374" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
#### Exercise `∃×-implies-×∃`
{:/}

#### 练习 `∃×-implies-×∃`

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明存在量词的合取蕴含了合取的存在量词：

<pre class="Agda">{% raw %}<a id="12594" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="12606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12606" class="Postulate">∃×-implies-×∃</a> <a id="12620" class="Symbol">:</a> <a id="12622" class="Symbol">∀</a> <a id="12624" class="Symbol">{</a><a id="12625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12625" class="Bound">A</a> <a id="12627" class="Symbol">:</a> <a id="12629" class="PrimitiveType">Set</a><a id="12632" class="Symbol">}</a> <a id="12634" class="Symbol">{</a><a id="12635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12635" class="Bound">B</a> <a id="12637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12637" class="Bound">C</a> <a id="12639" class="Symbol">:</a> <a id="12641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12625" class="Bound">A</a> <a id="12643" class="Symbol">→</a> <a id="12645" class="PrimitiveType">Set</a><a id="12648" class="Symbol">}</a> <a id="12650" class="Symbol">→</a>
    <a id="12656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12659" class="Bound">x</a> <a id="12661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12663" class="Symbol">(</a><a id="12664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12635" class="Bound">B</a> <a id="12666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12659" class="Bound">x</a> <a id="12668" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">×</a> <a id="12670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12637" class="Bound">C</a> <a id="12672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12659" class="Bound">x</a><a id="12673" class="Symbol">)</a> <a id="12675" class="Symbol">→</a> <a id="12677" class="Symbol">(</a><a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12681" class="Bound">x</a> <a id="12683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12635" class="Bound">B</a> <a id="12687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12681" class="Bound">x</a><a id="12688" class="Symbol">)</a> <a id="12690" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">×</a> <a id="12692" class="Symbol">(</a><a id="12693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="12696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12696" class="Bound">x</a> <a id="12698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="12700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12637" class="Bound">C</a> <a id="12702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12696" class="Bound">x</a><a id="12703" class="Symbol">)</a>{% endraw %}</pre>
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

反命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∃-⊎`
{:/}

#### 练习 `∃-⊎`

{::comment}
Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.
{:/}

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

{::comment}
## An existential example
{:/}

## 一个存在量化的例子

{::comment}
Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%}):
{:/}

回忆我们在 [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%}) 章节中定义的 `even` 和 `odd`：

<pre class="Agda">{% raw %}<a id="13306" class="Keyword">data</a> <a id="even"></a><a id="13311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="13316" class="Symbol">:</a> <a id="13318" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="13320" class="Symbol">→</a> <a id="13322" class="PrimitiveType">Set</a>
<a id="13326" class="Keyword">data</a> <a id="odd"></a><a id="13331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a>  <a id="13336" class="Symbol">:</a> <a id="13338" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="13340" class="Symbol">→</a> <a id="13342" class="PrimitiveType">Set</a>

<a id="13347" class="Keyword">data</a> <a id="13352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="13357" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13366" class="InductiveConstructor">even-zero</a> <a id="13376" class="Symbol">:</a> <a id="13378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="13383" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="13391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13391" class="InductiveConstructor">even-suc</a> <a id="13400" class="Symbol">:</a> <a id="13402" class="Symbol">∀</a> <a id="13404" class="Symbol">{</a><a id="13405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13405" class="Bound">n</a> <a id="13407" class="Symbol">:</a> <a id="13409" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13410" class="Symbol">}</a>
    <a id="13416" class="Symbol">→</a> <a id="13418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a> <a id="13422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13405" class="Bound">n</a>
      <a id="13430" class="Comment">------------</a>
    <a id="13447" class="Symbol">→</a> <a id="13449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="13454" class="Symbol">(</a><a id="13455" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13405" class="Bound">n</a><a id="13460" class="Symbol">)</a>

<a id="13463" class="Keyword">data</a> <a id="13468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a> <a id="13472" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="13480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13480" class="InductiveConstructor">odd-suc</a> <a id="13488" class="Symbol">:</a> <a id="13490" class="Symbol">∀</a> <a id="13492" class="Symbol">{</a><a id="13493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13493" class="Bound">n</a> <a id="13495" class="Symbol">:</a> <a id="13497" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13498" class="Symbol">}</a>
    <a id="13504" class="Symbol">→</a> <a id="13506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="13511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13493" class="Bound">n</a>
      <a id="13519" class="Comment">-----------</a>
    <a id="13535" class="Symbol">→</a> <a id="13537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a> <a id="13541" class="Symbol">(</a><a id="13542" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13493" class="Bound">n</a><a id="13547" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.
{:/}

如果一个数是 0 或者它是奇数的后继，那么这个数是偶数。如果一个数是偶数的后继，那么这个数是奇数。

{::comment}
We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:
{:/}

我们接下来要证明，一个数是偶数当且仅当这个数是一个数的两倍，一个数是奇数当且仅当这个数是一个数的两倍多一。换句话说，我们要证明的是：

{::comment}
`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`
{:/}

`even n`   当且仅当   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   当且仅当   `∃[ m ] (1 + m * 2 ≡ n)`

{::comment}
By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.
{:/}

惯例来说，我们往往将常数因子写在前面、将和里的常数项写在后面。但是这里我们没有按照惯例，而是反了过来，因为这样可以让证明更简单：

{::comment}
Here is the proof in the forward direction:
{:/}

这是向前方向的证明：

<pre class="Agda">{% raw %}<a id="even-∃"></a><a id="14558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14558" class="Function">even-∃</a> <a id="14565" class="Symbol">:</a> <a id="14567" class="Symbol">∀</a> <a id="14569" class="Symbol">{</a><a id="14570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14570" class="Bound">n</a> <a id="14572" class="Symbol">:</a> <a id="14574" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14575" class="Symbol">}</a> <a id="14577" class="Symbol">→</a> <a id="14579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="14584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14570" class="Bound">n</a> <a id="14586" class="Symbol">→</a> <a id="14588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="14591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14591" class="Bound">m</a> <a id="14593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="14595" class="Symbol">(</a>    <a id="14600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14591" class="Bound">m</a> <a id="14602" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">*</a> <a id="14604" class="Number">2</a> <a id="14606" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14570" class="Bound">n</a><a id="14609" class="Symbol">)</a>
<a id="odd-∃"></a><a id="14611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14611" class="Function">odd-∃</a>  <a id="14618" class="Symbol">:</a> <a id="14620" class="Symbol">∀</a> <a id="14622" class="Symbol">{</a><a id="14623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14623" class="Bound">n</a> <a id="14625" class="Symbol">:</a> <a id="14627" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14628" class="Symbol">}</a> <a id="14630" class="Symbol">→</a>  <a id="14633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a> <a id="14637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14623" class="Bound">n</a> <a id="14639" class="Symbol">→</a> <a id="14641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="14644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14644" class="Bound">m</a> <a id="14646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="14648" class="Symbol">(</a><a id="14649" class="Number">1</a> <a id="14651" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14644" class="Bound">m</a> <a id="14655" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">*</a> <a id="14657" class="Number">2</a> <a id="14659" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14623" class="Bound">n</a><a id="14662" class="Symbol">)</a>

<a id="14665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14558" class="Function">even-∃</a> <a id="14672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13366" class="InductiveConstructor">even-zero</a>                       <a id="14704" class="Symbol">=</a>  <a id="14707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="14709" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="14716" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="14721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>
<a id="14723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14558" class="Function">even-∃</a> <a id="14730" class="Symbol">(</a><a id="14731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13391" class="InductiveConstructor">even-suc</a> <a id="14740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14740" class="Bound">o</a><a id="14741" class="Symbol">)</a> <a id="14743" class="Keyword">with</a> <a id="14748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14611" class="Function">odd-∃</a> <a id="14754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14740" class="Bound">o</a>
<a id="14756" class="Symbol">...</a>                    <a id="14779" class="Symbol">|</a> <a id="14781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="14783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14783" class="Bound">m</a> <a id="14785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="14787" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="14792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>  <a id="14795" class="Symbol">=</a>  <a id="14798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="14800" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14783" class="Bound">m</a> <a id="14806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="14808" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="14813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>

<a id="14816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14611" class="Function">odd-∃</a>  <a id="14823" class="Symbol">(</a><a id="14824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13480" class="InductiveConstructor">odd-suc</a> <a id="14832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14832" class="Bound">e</a><a id="14833" class="Symbol">)</a>  <a id="14836" class="Keyword">with</a> <a id="14841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14558" class="Function">even-∃</a> <a id="14848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14832" class="Bound">e</a>
<a id="14850" class="Symbol">...</a>                    <a id="14873" class="Symbol">|</a> <a id="14875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="14877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14877" class="Bound">m</a> <a id="14879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="14881" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="14886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>  <a id="14889" class="Symbol">=</a>  <a id="14892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="14894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14877" class="Bound">m</a> <a id="14896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="14898" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="14903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>{% endraw %}</pre>
{::comment}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:
{:/}

我们定义两个相互递归的函数。给定 `n` 是奇数或者是偶数的证明，我们返回一个数
`m`，以及 `m * 2 ≡ n` 或者 `1 + m * 2 ≡ n` 的证明。我们根据 `n` 是奇数或者是偶数的证明进行归纳：

{::comment}
* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.
{:/}

* 如果这个数是偶数，因为它是 0，那么我们返回数据对 0 ，以及 0 的两倍是 0 的证明。

* 如果这个数是偶数，因为它是比一个奇数多 1，那么我们可以使用归纳假设，来获得一个数 `m` 和
`1 + m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `suc m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

* 如果这个数是奇数，因为它是一个偶数的后继，那么我们可以使用归纳假设，来获得一个数 `m` 和
`m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `1 + m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

{::comment}
This completes the proof in the forward direction.
{:/}

这样，我们就完成了向前方向的证明。

{::comment}
Here is the proof in the reverse direction:
{:/}

接下来是向后方向的证明：

<pre class="Agda">{% raw %}<a id="∃-even"></a><a id="16472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16472" class="Function">∃-even</a> <a id="16479" class="Symbol">:</a> <a id="16481" class="Symbol">∀</a> <a id="16483" class="Symbol">{</a><a id="16484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16484" class="Bound">n</a> <a id="16486" class="Symbol">:</a> <a id="16488" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16489" class="Symbol">}</a> <a id="16491" class="Symbol">→</a> <a id="16493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="16496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16496" class="Bound">m</a> <a id="16498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="16500" class="Symbol">(</a>    <a id="16505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16496" class="Bound">m</a> <a id="16507" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">*</a> <a id="16509" class="Number">2</a> <a id="16511" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16484" class="Bound">n</a><a id="16514" class="Symbol">)</a> <a id="16516" class="Symbol">→</a> <a id="16518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13311" class="Datatype">even</a> <a id="16523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16484" class="Bound">n</a>
<a id="∃-odd"></a><a id="16525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16525" class="Function">∃-odd</a>  <a id="16532" class="Symbol">:</a> <a id="16534" class="Symbol">∀</a> <a id="16536" class="Symbol">{</a><a id="16537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16537" class="Bound">n</a> <a id="16539" class="Symbol">:</a> <a id="16541" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16542" class="Symbol">}</a> <a id="16544" class="Symbol">→</a> <a id="16546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="16549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16549" class="Bound">m</a> <a id="16551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="16553" class="Symbol">(</a><a id="16554" class="Number">1</a> <a id="16556" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16549" class="Bound">m</a> <a id="16560" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">*</a> <a id="16562" class="Number">2</a> <a id="16564" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16537" class="Bound">n</a><a id="16567" class="Symbol">)</a> <a id="16569" class="Symbol">→</a>  <a id="16572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13331" class="Datatype">odd</a> <a id="16576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16537" class="Bound">n</a>

<a id="16579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16472" class="Function">∃-even</a> <a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a>  <a id="16589" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="16596" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="16601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>  <a id="16604" class="Symbol">=</a>  <a id="16607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13366" class="InductiveConstructor">even-zero</a>
<a id="16617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16472" class="Function">∃-even</a> <a id="16624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="16626" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16630" class="Bound">m</a> <a id="16632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="16634" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="16639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>  <a id="16642" class="Symbol">=</a>  <a id="16645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13391" class="InductiveConstructor">even-suc</a> <a id="16654" class="Symbol">(</a><a id="16655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16525" class="Function">∃-odd</a> <a id="16661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="16663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16630" class="Bound">m</a> <a id="16665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="16667" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="16672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a><a id="16673" class="Symbol">)</a>

<a id="16676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16525" class="Function">∃-odd</a>  <a id="16683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a>     <a id="16689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16689" class="Bound">m</a> <a id="16691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="16693" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="16698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a>  <a id="16701" class="Symbol">=</a>  <a id="16704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13480" class="InductiveConstructor">odd-suc</a> <a id="16712" class="Symbol">(</a><a id="16713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16472" class="Function">∃-even</a> <a id="16720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="16722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16689" class="Bound">m</a> <a id="16724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="16726" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a><a id="16732" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:
{:/}

给定一个是另一个数两倍的数，我们需要证明这个数是偶数。给定一个是另一个数两倍多一的数，我们需要证明这个数是奇数。我们对于存在量化的证明进行归纳。在偶数的情况，我们也需要考虑两种一个数是另一个数两倍的情况。

{::comment}
- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.
{:/}

- 在偶数是 `zero` 的情况中，我们需要证明 `zero * 2` 是偶数，由 `even-zero` 可得。

- 在偶数是 `suc n` 的情况中，我们需要证明 `suc m * 2` 是偶数。归纳假设告诉我们，
`1 + m * 2` 是奇数，那么所求证的结果由 `even-suc` 可得。

- 在偶数的情况中，我们需要证明 `1 + m * 2` 是奇数。归纳假设告诉我们，`m * 2` 是偶数，那么所求证的结果由 `odd-suc` 可得。

{::comment}
This completes the proof in the backward direction.
{:/}

这样，我们就完成了向后方向的证明。

{::comment}
#### Exercise `∃-even-odd`
{:/}

#### 练习 `∃-even-odd`

{::comment}
How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.
{:/}

如果我们用 `m * 2` 代替 `2 * m`，`1 + m * 2` 代替 `2 * m + 1`，上述证明会变得复杂多少呢？用这种方法来重写 `∃-even` 和 `∃-odd`。

{::comment}
<pre class="Agda">{% raw %}<a id="18318" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="18371" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `∃-+-≤`
{:/}

#### 练习 `∃-+-≤`

{::comment}
Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.
{:/}

证明 `y ≤ z` 当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时成立。

{::comment}
<pre class="Agda">{% raw %}<a id="18624" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="18677" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
## Existentials, Universals, and Negation
{:/}

## 存在量化、全程量化和否定

{::comment}
Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{:/}

存在量化的否定与否定的全程量化是同构的。考虑到存在量化是析构的推广，全程量化是合构的推广，这样的结果与析构的否定与否定的合构是同构的结果相似。

<pre class="Agda">{% raw %}<a id="¬∃≃∀¬"></a><a id="19187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19187" class="Function">¬∃≃∀¬</a> <a id="19193" class="Symbol">:</a> <a id="19195" class="Symbol">∀</a> <a id="19197" class="Symbol">{</a><a id="19198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19198" class="Bound">A</a> <a id="19200" class="Symbol">:</a> <a id="19202" class="PrimitiveType">Set</a><a id="19205" class="Symbol">}</a> <a id="19207" class="Symbol">{</a><a id="19208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19208" class="Bound">B</a> <a id="19210" class="Symbol">:</a> <a id="19212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19198" class="Bound">A</a> <a id="19214" class="Symbol">→</a> <a id="19216" class="PrimitiveType">Set</a><a id="19219" class="Symbol">}</a>
  <a id="19223" class="Symbol">→</a> <a id="19225" class="Symbol">(</a><a id="19226" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="19228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="19231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19231" class="Bound">x</a> <a id="19233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="19235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19208" class="Bound">B</a> <a id="19237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19231" class="Bound">x</a><a id="19238" class="Symbol">)</a> <a id="19240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="19242" class="Symbol">∀</a> <a id="19244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19244" class="Bound">x</a> <a id="19246" class="Symbol">→</a> <a id="19248" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="19250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19208" class="Bound">B</a> <a id="19252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19244" class="Bound">x</a>
<a id="19254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19187" class="Function">¬∃≃∀¬</a> <a id="19260" class="Symbol">=</a>
  <a id="19264" class="Keyword">record</a>
    <a id="19275" class="Symbol">{</a> <a id="19277" class="Field">to</a>      <a id="19285" class="Symbol">=</a>  <a id="19288" class="Symbol">λ{</a> <a id="19291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19291" class="Bound">¬∃xy</a> <a id="19296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19296" class="Bound">x</a> <a id="19298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19298" class="Bound">y</a> <a id="19300" class="Symbol">→</a> <a id="19302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19291" class="Bound">¬∃xy</a> <a id="19307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="19309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19296" class="Bound">x</a> <a id="19311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="19313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19298" class="Bound">y</a> <a id="19315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="19317" class="Symbol">}</a>
    <a id="19323" class="Symbol">;</a> <a id="19325" class="Field">from</a>    <a id="19333" class="Symbol">=</a>  <a id="19336" class="Symbol">λ{</a> <a id="19339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19339" class="Bound">∀¬xy</a> <a id="19344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="19346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19346" class="Bound">x</a> <a id="19348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="19350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19350" class="Bound">y</a> <a id="19352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="19354" class="Symbol">→</a> <a id="19356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19339" class="Bound">∀¬xy</a> <a id="19361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19346" class="Bound">x</a> <a id="19363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19350" class="Bound">y</a> <a id="19365" class="Symbol">}</a>
    <a id="19371" class="Symbol">;</a> <a id="19373" class="Field">from∘to</a> <a id="19381" class="Symbol">=</a>  <a id="19384" class="Symbol">λ{</a> <a id="19387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19387" class="Bound">¬∃xy</a> <a id="19392" class="Symbol">→</a> <a id="19394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a> <a id="19409" class="Symbol">λ{</a> <a id="19412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟨</a> <a id="19414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19414" class="Bound">x</a> <a id="19416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">,</a> <a id="19418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19418" class="Bound">y</a> <a id="19420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6640" class="InductiveConstructor Operator">⟩</a> <a id="19422" class="Symbol">→</a> <a id="19424" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="19429" class="Symbol">}</a> <a id="19431" class="Symbol">}</a>
    <a id="19437" class="Symbol">;</a> <a id="19439" class="Field">to∘from</a> <a id="19447" class="Symbol">=</a>  <a id="19450" class="Symbol">λ{</a> <a id="19453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19453" class="Bound">∀¬xy</a> <a id="19458" class="Symbol">→</a> <a id="19460" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a> <a id="19465" class="Symbol">}</a>
    <a id="19471" class="Symbol">}</a>{% endraw %}</pre>
{::comment}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.
{:/}

在 `to` 的方向，给定了一个 `¬ ∃[ x ] B x` 类型的值 `¬∃xy`，需要证明给定一个 `x` 的值，可以推导出 `¬ B x`。换句话说，给定一个 `B x` 类型的值 `y`，我们可以推导出假。将 `x` 和 `y`
合并起来我们就得到了 `∃[ x ] B x` 类型的值 `⟨ x , y ⟩`，对其使用 `¬∃xy` 即可获得矛盾。

{::comment}
In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.
{:/}

在 `from` 的方向，给定了一个 `∀ x → ¬ B x` 类型的值 `∀¬xy`，需要证明从一个类型为
`∃[ x ] B x` 类型的值 `⟨ x , y ⟩` ，我们可以推导出假。将 `∀¬xy` 使用于 `x` 之上，可以得到类型为 `¬ B x` 的值，对其使用 `y` 即可获得矛盾。

{::comment}
The two inverse proofs are straightforward, where one direction
requires extensionality.
{:/}

两个逆的证明很直接，其中有一个方向需要外延性。

{::comment}
#### Exercise `∃¬-implies-¬∀` (recommended)
{:/}

#### 练习 `∃¬-implies-¬∀` （推荐）

{::comment}
Show that existential of a negation implies negation of a universal:
{:/}

证明否定的存在量化蕴含了全程量化的否定：

<pre class="Agda">{% raw %}<a id="20803" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="20815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20815" class="Postulate">∃¬-implies-¬∀</a> <a id="20829" class="Symbol">:</a> <a id="20831" class="Symbol">∀</a> <a id="20833" class="Symbol">{</a><a id="20834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20834" class="Bound">A</a> <a id="20836" class="Symbol">:</a> <a id="20838" class="PrimitiveType">Set</a><a id="20841" class="Symbol">}</a> <a id="20843" class="Symbol">{</a><a id="20844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20844" class="Bound">B</a> <a id="20846" class="Symbol">:</a> <a id="20848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20834" class="Bound">A</a> <a id="20850" class="Symbol">→</a> <a id="20852" class="PrimitiveType">Set</a><a id="20855" class="Symbol">}</a>
    <a id="20861" class="Symbol">→</a> <a id="20863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">∃[</a> <a id="20866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20866" class="Bound">x</a> <a id="20868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10033" class="Function">]</a> <a id="20870" class="Symbol">(</a><a id="20871" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="20873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20844" class="Bound">B</a> <a id="20875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20866" class="Bound">x</a><a id="20876" class="Symbol">)</a>
      <a id="20884" class="Comment">--------------</a>
    <a id="20903" class="Symbol">→</a> <a id="20905" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="20907" class="Symbol">(∀</a> <a id="20910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20910" class="Bound">x</a> <a id="20912" class="Symbol">→</a> <a id="20914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20844" class="Bound">B</a> <a id="20916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20910" class="Bound">x</a><a id="20917" class="Symbol">)</a>{% endraw %}</pre>
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

{::comment}
#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}
{:/}

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin),
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}{% link out/plfa/Relations.md%}#Bin-predicates)
define a datatype of bitstrings representing natural numbers:
{:/}

回忆在练习 [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)、
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws) 和
[Bin-predicates]({{ site.baseurl }}{% link out/plfa/Relations.md%}#Bin-predicates) 中，我们定义了比特串的数据类型来表示自然数：

<pre class="Agda">{% raw %}<a id="21540" class="Keyword">data</a> <a id="Bin"></a><a id="21545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a> <a id="21549" class="Symbol">:</a> <a id="21551" class="PrimitiveType">Set</a> <a id="21555" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="21563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21563" class="InductiveConstructor">nil</a> <a id="21567" class="Symbol">:</a> <a id="21569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="21575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21575" class="InductiveConstructor Operator">x0_</a> <a id="21579" class="Symbol">:</a> <a id="21581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a> <a id="21585" class="Symbol">→</a> <a id="21587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="21593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21593" class="InductiveConstructor Operator">x1_</a> <a id="21597" class="Symbol">:</a> <a id="21599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a> <a id="21603" class="Symbol">→</a> <a id="21605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21545" class="Datatype">Bin</a>{% endraw %}</pre>
{::comment}
And ask you to define the following functions and predicates:
{:/}

并要求你来定义下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

{::comment}
And to establish the following properties:
{:/}

以及证明下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.
{:/}

使用上述，证明 `ℕ` 与 `∃[ x ](Can x)` 之间存在同构。

{::comment}
<pre class="Agda">{% raw %}<a id="22123" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="22176" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

<pre class="Agda">{% raw %}<a id="22382" class="Keyword">import</a> <a id="22389" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html" class="Module">Data.Product</a> <a id="22402" class="Keyword">using</a> <a id="22408" class="Symbol">(</a><a id="22409" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#69" class="Record">Σ</a><a id="22410" class="Symbol">;</a> <a id="22412" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">_,_</a><a id="22415" class="Symbol">;</a> <a id="22417" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#881" class="Function">∃</a><a id="22418" class="Symbol">;</a> <a id="22420" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#764" class="Function">Σ-syntax</a><a id="22428" class="Symbol">;</a> <a id="22430" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#942" class="Function">∃-syntax</a><a id="22438" class="Symbol">)</a>{% endraw %}</pre>


## Unicode

{::comment}
This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)

{:/}

本章节使用下列 Unicode：

    Π  U+03A0  希腊大写字母 PI (\Pi)
    Σ  U+03A3  希腊大写字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
