---
src       : src/plfa/Isomorphism.lagda
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="194" class="Keyword">module</a> <a id="201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="218" class="Keyword">where</a>{% endraw %}</pre>

{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

本部分介绍同构（Isomorphism）与嵌入（Embedding）。同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。


{::comment}
## Imports
{:/}

## 导入

<pre class="Agda">{% raw %}<a id="768" class="Keyword">import</a> <a id="775" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="813" class="Symbol">as</a> <a id="816" class="Module">Eq</a>
<a id="819" class="Keyword">open</a> <a id="824" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="827" class="Keyword">using</a> <a id="833" class="Symbol">(</a><a id="834" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="837" class="Symbol">;</a> <a id="839" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="843" class="Symbol">;</a> <a id="845" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="849" class="Symbol">;</a> <a id="851" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a><a id="859" class="Symbol">)</a>
<a id="861" class="Keyword">open</a> <a id="866" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a>
<a id="881" class="Keyword">open</a> <a id="886" class="Keyword">import</a> <a id="893" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="902" class="Keyword">using</a> <a id="908" class="Symbol">(</a><a id="909" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="910" class="Symbol">;</a> <a id="912" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="916" class="Symbol">;</a> <a id="918" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="921" class="Symbol">;</a> <a id="923" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="926" class="Symbol">)</a>
<a id="928" class="Keyword">open</a> <a id="933" class="Keyword">import</a> <a id="940" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="960" class="Keyword">using</a> <a id="966" class="Symbol">(</a><a id="967" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="973" class="Symbol">)</a>{% endraw %}</pre>


{::comment}
## Lambda expressions
{:/}

## Lambda 表达式

{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。

{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

{::comment}
is equivalent to a function `f` defined by the equations
{:/}

等同于定义一个函数 `f`，使用下列等式：

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。

{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：

    λ x → N

{::comment}
or
{:/}

或者

    λ (x : A) → N

{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。

{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。


{::comment}
## Function composition
{:/}

## 函数组合 （Function Composition）

{::comment}
In what follows, we will make use of function composition:
{:/}

接下来，我们将使用函数组合：

<pre class="Agda">{% raw %}<a id="_∘_"></a><a id="2744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">_∘_</a> <a id="2748" class="Symbol">:</a> <a id="2750" class="Symbol">∀</a> <a id="2752" class="Symbol">{</a><a id="2753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2753" class="Bound">A</a> <a id="2755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2755" class="Bound">B</a> <a id="2757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2757" class="Bound">C</a> <a id="2759" class="Symbol">:</a> <a id="2761" class="PrimitiveType">Set</a><a id="2764" class="Symbol">}</a> <a id="2766" class="Symbol">→</a> <a id="2768" class="Symbol">(</a><a id="2769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2755" class="Bound">B</a> <a id="2771" class="Symbol">→</a> <a id="2773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2757" class="Bound">C</a><a id="2774" class="Symbol">)</a> <a id="2776" class="Symbol">→</a> <a id="2778" class="Symbol">(</a><a id="2779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2753" class="Bound">A</a> <a id="2781" class="Symbol">→</a> <a id="2783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2755" class="Bound">B</a><a id="2784" class="Symbol">)</a> <a id="2786" class="Symbol">→</a> <a id="2788" class="Symbol">(</a><a id="2789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2753" class="Bound">A</a> <a id="2791" class="Symbol">→</a> <a id="2793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2757" class="Bound">C</a><a id="2794" class="Symbol">)</a>
<a id="2796" class="Symbol">(</a><a id="2797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2797" class="Bound">g</a> <a id="2799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="2801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2801" class="Bound">f</a><a id="2802" class="Symbol">)</a> <a id="2804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2804" class="Bound">x</a>  <a id="2807" class="Symbol">=</a> <a id="2809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2797" class="Bound">g</a> <a id="2811" class="Symbol">(</a><a id="2812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2801" class="Bound">f</a> <a id="2814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2804" class="Bound">x</a><a id="2815" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}

`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。一个等价的定义，使用 lambda 表达式，如下：

<pre class="Agda">{% raw %}<a id="_∘′_"></a><a id="3070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3070" class="Function Operator">_∘′_</a> <a id="3075" class="Symbol">:</a> <a id="3077" class="Symbol">∀</a> <a id="3079" class="Symbol">{</a><a id="3080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3080" class="Bound">A</a> <a id="3082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3082" class="Bound">B</a> <a id="3084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3084" class="Bound">C</a> <a id="3086" class="Symbol">:</a> <a id="3088" class="PrimitiveType">Set</a><a id="3091" class="Symbol">}</a> <a id="3093" class="Symbol">→</a> <a id="3095" class="Symbol">(</a><a id="3096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3082" class="Bound">B</a> <a id="3098" class="Symbol">→</a> <a id="3100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3084" class="Bound">C</a><a id="3101" class="Symbol">)</a> <a id="3103" class="Symbol">→</a> <a id="3105" class="Symbol">(</a><a id="3106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3080" class="Bound">A</a> <a id="3108" class="Symbol">→</a> <a id="3110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3082" class="Bound">B</a><a id="3111" class="Symbol">)</a> <a id="3113" class="Symbol">→</a> <a id="3115" class="Symbol">(</a><a id="3116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3080" class="Bound">A</a> <a id="3118" class="Symbol">→</a> <a id="3120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3084" class="Bound">C</a><a id="3121" class="Symbol">)</a>
<a id="3123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3123" class="Bound">g</a> <a id="3125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3070" class="Function Operator">∘′</a> <a id="3128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3128" class="Bound">f</a>  <a id="3131" class="Symbol">=</a>  <a id="3134" class="Symbol">λ</a> <a id="3136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3136" class="Bound">x</a> <a id="3138" class="Symbol">→</a> <a id="3140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3123" class="Bound">g</a> <a id="3142" class="Symbol">(</a><a id="3143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3128" class="Bound">f</a> <a id="3145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3136" class="Bound">x</a><a id="3146" class="Symbol">)</a>{% endraw %}</pre>


{::comment}
## Extensionality {#extensionality}
{:/}

## 外延性（Extensionality） {#extensionality}

{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier]({{ site.baseurl }}{% link out/plfa/Equality.md%}#cong).
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，那么两个函数相同。这是 `cong-app` 的逆命题，在[之前]({{ site.baseurl }}{% link out/plfa/Equality.md%}#cong)有所介绍。

{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}

Agda 并不预设外延性，但我们可以假设其成立：

<pre class="Agda">{% raw %}<a id="3789" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="3801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a> <a id="3816" class="Symbol">:</a> <a id="3818" class="Symbol">∀</a> <a id="3820" class="Symbol">{</a><a id="3821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3821" class="Bound">A</a> <a id="3823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3823" class="Bound">B</a> <a id="3825" class="Symbol">:</a> <a id="3827" class="PrimitiveType">Set</a><a id="3830" class="Symbol">}</a> <a id="3832" class="Symbol">{</a><a id="3833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3833" class="Bound">f</a> <a id="3835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3835" class="Bound">g</a> <a id="3837" class="Symbol">:</a> <a id="3839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3821" class="Bound">A</a> <a id="3841" class="Symbol">→</a> <a id="3843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3823" class="Bound">B</a><a id="3844" class="Symbol">}</a>
    <a id="3850" class="Symbol">→</a> <a id="3852" class="Symbol">(∀</a> <a id="3855" class="Symbol">(</a><a id="3856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3856" class="Bound">x</a> <a id="3858" class="Symbol">:</a> <a id="3860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3821" class="Bound">A</a><a id="3861" class="Symbol">)</a> <a id="3863" class="Symbol">→</a> <a id="3865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3833" class="Bound">f</a> <a id="3867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3856" class="Bound">x</a> <a id="3869" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3835" class="Bound">g</a> <a id="3873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3856" class="Bound">x</a><a id="3874" class="Symbol">)</a>
      <a id="3882" class="Comment">-----------------------</a>
    <a id="3910" class="Symbol">→</a> <a id="3912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3833" class="Bound">f</a> <a id="3914" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3835" class="Bound">g</a>{% endraw %}</pre>

{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.
{:/}

假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。

{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals]({{ site.baseurl }}{% link out/plfa/Naturals.md%}),
and one where it is defined the other way around.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals]({{ site.baseurl }}{% link out/plfa/Naturals.md%})
章节中那样定义，另一个如下，反过来定义：

<pre class="Agda">{% raw %}<a id="_+′_"></a><a id="4408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">_+′_</a> <a id="4413" class="Symbol">:</a> <a id="4415" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="4417" class="Symbol">→</a> <a id="4419" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="4421" class="Symbol">→</a> <a id="4423" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a>
<a id="4425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4425" class="Bound">m</a> <a id="4427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">+′</a> <a id="4430" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>  <a id="4436" class="Symbol">=</a> <a id="4438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4425" class="Bound">m</a>
<a id="4440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4440" class="Bound">m</a> <a id="4442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">+′</a> <a id="4445" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4449" class="Bound">n</a> <a id="4451" class="Symbol">=</a> <a id="4453" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4457" class="Symbol">(</a><a id="4458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4440" class="Bound">m</a> <a id="4460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">+′</a> <a id="4463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4449" class="Bound">n</a><a id="4464" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}

通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，会返回相同的值：

<pre class="Agda">{% raw %}<a id="same-app"></a><a id="4673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4673" class="Function">same-app</a> <a id="4682" class="Symbol">:</a> <a id="4684" class="Symbol">∀</a> <a id="4686" class="Symbol">(</a><a id="4687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4687" class="Bound">m</a> <a id="4689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4689" class="Bound">n</a> <a id="4691" class="Symbol">:</a> <a id="4693" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4694" class="Symbol">)</a> <a id="4696" class="Symbol">→</a> <a id="4698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4687" class="Bound">m</a> <a id="4700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">+′</a> <a id="4703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4689" class="Bound">n</a> <a id="4705" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4687" class="Bound">m</a> <a id="4709" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="4711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4689" class="Bound">n</a>
<a id="4713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4673" class="Function">same-app</a> <a id="4722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4722" class="Bound">m</a> <a id="4724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4724" class="Bound">n</a> <a id="4726" class="Keyword">rewrite</a> <a id="4734" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="4741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4722" class="Bound">m</a> <a id="4743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4724" class="Bound">n</a> <a id="4745" class="Symbol">=</a> <a id="4747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4768" class="Function">helper</a> <a id="4754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4722" class="Bound">m</a> <a id="4756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4724" class="Bound">n</a>
  <a id="4760" class="Keyword">where</a>
  <a id="4768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4768" class="Function">helper</a> <a id="4775" class="Symbol">:</a> <a id="4777" class="Symbol">∀</a> <a id="4779" class="Symbol">(</a><a id="4780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4780" class="Bound">m</a> <a id="4782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4782" class="Bound">n</a> <a id="4784" class="Symbol">:</a> <a id="4786" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4787" class="Symbol">)</a> <a id="4789" class="Symbol">→</a> <a id="4791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4780" class="Bound">m</a> <a id="4793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">+′</a> <a id="4796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4782" class="Bound">n</a> <a id="4798" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4782" class="Bound">n</a> <a id="4802" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="4804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4780" class="Bound">m</a>
  <a id="4808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4768" class="Function">helper</a> <a id="4815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4815" class="Bound">m</a> <a id="4817" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="4825" class="Symbol">=</a> <a id="4827" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
  <a id="4834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4768" class="Function">helper</a> <a id="4841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4841" class="Bound">m</a> <a id="4843" class="Symbol">(</a><a id="4844" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4848" class="Bound">n</a><a id="4849" class="Symbol">)</a> <a id="4851" class="Symbol">=</a> <a id="4853" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="4858" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4862" class="Symbol">(</a><a id="4863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4768" class="Function">helper</a> <a id="4870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4841" class="Bound">m</a> <a id="4872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4848" class="Bound">n</a><a id="4873" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：

<pre class="Agda">{% raw %}<a id="same"></a><a id="5108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5108" class="Function">same</a> <a id="5113" class="Symbol">:</a> <a id="5115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4408" class="Function Operator">_+′_</a> <a id="5120" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5122" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a>
<a id="5126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5108" class="Function">same</a> <a id="5131" class="Symbol">=</a> <a id="5133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a> <a id="5148" class="Symbol">(λ</a> <a id="5151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5151" class="Bound">m</a> <a id="5153" class="Symbol">→</a> <a id="5155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3801" class="Postulate">extensionality</a> <a id="5170" class="Symbol">(λ</a> <a id="5173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5173" class="Bound">n</a> <a id="5175" class="Symbol">→</a> <a id="5177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4673" class="Function">same-app</a> <a id="5186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5151" class="Bound">m</a> <a id="5188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5173" class="Bound">n</a><a id="5189" class="Symbol">))</a>{% endraw %}</pre>

{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}

我们偶尔需要在之后的情况中假设外延性。


{::comment}
## Isomorphism
{:/}

## 同构（Isomorphism）

{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。下面是同构的正式定义：

<pre class="Agda">{% raw %}<a id="5542" class="Keyword">infix</a> <a id="5548" class="Number">0</a> <a id="5550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">_≃_</a>
<a id="5554" class="Keyword">record</a> <a id="_≃_"></a><a id="5561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">_≃_</a> <a id="5565" class="Symbol">(</a><a id="5566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5566" class="Bound">A</a> <a id="5568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5568" class="Bound">B</a> <a id="5570" class="Symbol">:</a> <a id="5572" class="PrimitiveType">Set</a><a id="5575" class="Symbol">)</a> <a id="5577" class="Symbol">:</a> <a id="5579" class="PrimitiveType">Set</a> <a id="5583" class="Keyword">where</a>
  <a id="5591" class="Keyword">field</a>
    <a id="_≃_.to"></a><a id="5601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a>   <a id="5606" class="Symbol">:</a> <a id="5608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5566" class="Bound">A</a> <a id="5610" class="Symbol">→</a> <a id="5612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5568" class="Bound">B</a>
    <a id="_≃_.from"></a><a id="5618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="5623" class="Symbol">:</a> <a id="5625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5568" class="Bound">B</a> <a id="5627" class="Symbol">→</a> <a id="5629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5566" class="Bound">A</a>
    <a id="_≃_.from∘to"></a><a id="5635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5635" class="Field">from∘to</a> <a id="5643" class="Symbol">:</a> <a id="5645" class="Symbol">∀</a> <a id="5647" class="Symbol">(</a><a id="5648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5648" class="Bound">x</a> <a id="5650" class="Symbol">:</a> <a id="5652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5566" class="Bound">A</a><a id="5653" class="Symbol">)</a> <a id="5655" class="Symbol">→</a> <a id="5657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="5662" class="Symbol">(</a><a id="5663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="5666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5648" class="Bound">x</a><a id="5667" class="Symbol">)</a> <a id="5669" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5648" class="Bound">x</a>
    <a id="_≃_.to∘from"></a><a id="5677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5677" class="Field">to∘from</a> <a id="5685" class="Symbol">:</a> <a id="5687" class="Symbol">∀</a> <a id="5689" class="Symbol">(</a><a id="5690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5690" class="Bound">y</a> <a id="5692" class="Symbol">:</a> <a id="5694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5568" class="Bound">B</a><a id="5695" class="Symbol">)</a> <a id="5697" class="Symbol">→</a> <a id="5699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="5702" class="Symbol">(</a><a id="5703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="5708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5690" class="Bound">y</a><a id="5709" class="Symbol">)</a> <a id="5711" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5690" class="Bound">y</a>
<a id="5715" class="Keyword">open</a> <a id="5720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Module Operator">_≃_</a>{% endraw %}</pre>

{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。

{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：

<pre class="Agda">{% raw %}<a id="6901" class="Keyword">data</a> <a id="_≃′_"></a><a id="6906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">_≃′_</a> <a id="6911" class="Symbol">(</a><a id="6912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6912" class="Bound">A</a> <a id="6914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6914" class="Bound">B</a> <a id="6916" class="Symbol">:</a> <a id="6918" class="PrimitiveType">Set</a><a id="6921" class="Symbol">):</a> <a id="6924" class="PrimitiveType">Set</a> <a id="6928" class="Keyword">where</a>
  <a id="_≃′_.mk-≃′"></a><a id="6936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6936" class="InductiveConstructor">mk-≃′</a> <a id="6942" class="Symbol">:</a> <a id="6944" class="Symbol">∀</a> <a id="6946" class="Symbol">(</a><a id="6947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6947" class="Bound">to</a> <a id="6950" class="Symbol">:</a> <a id="6952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6912" class="Bound">A</a> <a id="6954" class="Symbol">→</a> <a id="6956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6914" class="Bound">B</a><a id="6957" class="Symbol">)</a> <a id="6959" class="Symbol">→</a>
          <a id="6971" class="Symbol">∀</a> <a id="6973" class="Symbol">(</a><a id="6974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6974" class="Bound">from</a> <a id="6979" class="Symbol">:</a> <a id="6981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6914" class="Bound">B</a> <a id="6983" class="Symbol">→</a> <a id="6985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6912" class="Bound">A</a><a id="6986" class="Symbol">)</a> <a id="6988" class="Symbol">→</a>
          <a id="7000" class="Symbol">∀</a> <a id="7002" class="Symbol">(</a><a id="7003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7003" class="Bound">from∘to</a> <a id="7011" class="Symbol">:</a> <a id="7013" class="Symbol">(∀</a> <a id="7016" class="Symbol">(</a><a id="7017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7017" class="Bound">x</a> <a id="7019" class="Symbol">:</a> <a id="7021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6912" class="Bound">A</a><a id="7022" class="Symbol">)</a> <a id="7024" class="Symbol">→</a> <a id="7026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6974" class="Bound">from</a> <a id="7031" class="Symbol">(</a><a id="7032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6947" class="Bound">to</a> <a id="7035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7017" class="Bound">x</a><a id="7036" class="Symbol">)</a> <a id="7038" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7017" class="Bound">x</a><a id="7041" class="Symbol">))</a> <a id="7044" class="Symbol">→</a>
          <a id="7056" class="Symbol">∀</a> <a id="7058" class="Symbol">(</a><a id="7059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7059" class="Bound">to∘from</a> <a id="7067" class="Symbol">:</a> <a id="7069" class="Symbol">(∀</a> <a id="7072" class="Symbol">(</a><a id="7073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7073" class="Bound">y</a> <a id="7075" class="Symbol">:</a> <a id="7077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6914" class="Bound">B</a><a id="7078" class="Symbol">)</a> <a id="7080" class="Symbol">→</a> <a id="7082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6947" class="Bound">to</a> <a id="7085" class="Symbol">(</a><a id="7086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6974" class="Bound">from</a> <a id="7091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7073" class="Bound">y</a><a id="7092" class="Symbol">)</a> <a id="7094" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7073" class="Bound">y</a><a id="7097" class="Symbol">))</a> <a id="7100" class="Symbol">→</a>
          <a id="7112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6912" class="Bound">A</a> <a id="7114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">≃′</a> <a id="7117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6914" class="Bound">B</a>

<a id="to′"></a><a id="7120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7120" class="Function">to′</a> <a id="7124" class="Symbol">:</a> <a id="7126" class="Symbol">∀</a> <a id="7128" class="Symbol">{</a><a id="7129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7129" class="Bound">A</a> <a id="7131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7131" class="Bound">B</a> <a id="7133" class="Symbol">:</a> <a id="7135" class="PrimitiveType">Set</a><a id="7138" class="Symbol">}</a> <a id="7140" class="Symbol">→</a> <a id="7142" class="Symbol">(</a><a id="7143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7129" class="Bound">A</a> <a id="7145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">≃′</a> <a id="7148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7131" class="Bound">B</a><a id="7149" class="Symbol">)</a> <a id="7151" class="Symbol">→</a> <a id="7153" class="Symbol">(</a><a id="7154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7129" class="Bound">A</a> <a id="7156" class="Symbol">→</a> <a id="7158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7131" class="Bound">B</a><a id="7159" class="Symbol">)</a>
<a id="7161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7120" class="Function">to′</a> <a id="7165" class="Symbol">(</a><a id="7166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6936" class="InductiveConstructor">mk-≃′</a> <a id="7172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7172" class="Bound">f</a> <a id="7174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7174" class="Bound">g</a> <a id="7176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7176" class="Bound">g∘f</a> <a id="7180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7180" class="Bound">f∘g</a><a id="7183" class="Symbol">)</a> <a id="7185" class="Symbol">=</a> <a id="7187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7172" class="Bound">f</a>

<a id="from′"></a><a id="7190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7190" class="Function">from′</a> <a id="7196" class="Symbol">:</a> <a id="7198" class="Symbol">∀</a> <a id="7200" class="Symbol">{</a><a id="7201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7201" class="Bound">A</a> <a id="7203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7203" class="Bound">B</a> <a id="7205" class="Symbol">:</a> <a id="7207" class="PrimitiveType">Set</a><a id="7210" class="Symbol">}</a> <a id="7212" class="Symbol">→</a> <a id="7214" class="Symbol">(</a><a id="7215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7201" class="Bound">A</a> <a id="7217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">≃′</a> <a id="7220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7203" class="Bound">B</a><a id="7221" class="Symbol">)</a> <a id="7223" class="Symbol">→</a> <a id="7225" class="Symbol">(</a><a id="7226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7203" class="Bound">B</a> <a id="7228" class="Symbol">→</a> <a id="7230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7201" class="Bound">A</a><a id="7231" class="Symbol">)</a>
<a id="7233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7190" class="Function">from′</a> <a id="7239" class="Symbol">(</a><a id="7240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6936" class="InductiveConstructor">mk-≃′</a> <a id="7246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7246" class="Bound">f</a> <a id="7248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7248" class="Bound">g</a> <a id="7250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7250" class="Bound">g∘f</a> <a id="7254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7254" class="Bound">f∘g</a><a id="7257" class="Symbol">)</a> <a id="7259" class="Symbol">=</a> <a id="7261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7248" class="Bound">g</a>

<a id="from∘to′"></a><a id="7264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7264" class="Function">from∘to′</a> <a id="7273" class="Symbol">:</a> <a id="7275" class="Symbol">∀</a> <a id="7277" class="Symbol">{</a><a id="7278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7278" class="Bound">A</a> <a id="7280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7280" class="Bound">B</a> <a id="7282" class="Symbol">:</a> <a id="7284" class="PrimitiveType">Set</a><a id="7287" class="Symbol">}</a> <a id="7289" class="Symbol">→</a> <a id="7291" class="Symbol">(</a><a id="7292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7292" class="Bound">A≃B</a> <a id="7296" class="Symbol">:</a> <a id="7298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7278" class="Bound">A</a> <a id="7300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">≃′</a> <a id="7303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7280" class="Bound">B</a><a id="7304" class="Symbol">)</a> <a id="7306" class="Symbol">→</a> <a id="7308" class="Symbol">(∀</a> <a id="7311" class="Symbol">(</a><a id="7312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7312" class="Bound">x</a> <a id="7314" class="Symbol">:</a> <a id="7316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7278" class="Bound">A</a><a id="7317" class="Symbol">)</a> <a id="7319" class="Symbol">→</a> <a id="7321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7190" class="Function">from′</a> <a id="7327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7292" class="Bound">A≃B</a> <a id="7331" class="Symbol">(</a><a id="7332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7120" class="Function">to′</a> <a id="7336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7292" class="Bound">A≃B</a> <a id="7340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7312" class="Bound">x</a><a id="7341" class="Symbol">)</a> <a id="7343" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7312" class="Bound">x</a><a id="7346" class="Symbol">)</a>
<a id="7348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7264" class="Function">from∘to′</a> <a id="7357" class="Symbol">(</a><a id="7358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6936" class="InductiveConstructor">mk-≃′</a> <a id="7364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7364" class="Bound">f</a> <a id="7366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7366" class="Bound">g</a> <a id="7368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7368" class="Bound">g∘f</a> <a id="7372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7372" class="Bound">f∘g</a><a id="7375" class="Symbol">)</a> <a id="7377" class="Symbol">=</a> <a id="7379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7368" class="Bound">g∘f</a>

<a id="to∘from′"></a><a id="7384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7384" class="Function">to∘from′</a> <a id="7393" class="Symbol">:</a> <a id="7395" class="Symbol">∀</a> <a id="7397" class="Symbol">{</a><a id="7398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7398" class="Bound">A</a> <a id="7400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7400" class="Bound">B</a> <a id="7402" class="Symbol">:</a> <a id="7404" class="PrimitiveType">Set</a><a id="7407" class="Symbol">}</a> <a id="7409" class="Symbol">→</a> <a id="7411" class="Symbol">(</a><a id="7412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7412" class="Bound">A≃B</a> <a id="7416" class="Symbol">:</a> <a id="7418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7398" class="Bound">A</a> <a id="7420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Datatype Operator">≃′</a> <a id="7423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7400" class="Bound">B</a><a id="7424" class="Symbol">)</a> <a id="7426" class="Symbol">→</a> <a id="7428" class="Symbol">(∀</a> <a id="7431" class="Symbol">(</a><a id="7432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7432" class="Bound">y</a> <a id="7434" class="Symbol">:</a> <a id="7436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7400" class="Bound">B</a><a id="7437" class="Symbol">)</a> <a id="7439" class="Symbol">→</a> <a id="7441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7120" class="Function">to′</a> <a id="7445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7412" class="Bound">A≃B</a> <a id="7449" class="Symbol">(</a><a id="7450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7190" class="Function">from′</a> <a id="7456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7412" class="Bound">A≃B</a> <a id="7460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7432" class="Bound">y</a><a id="7461" class="Symbol">)</a> <a id="7463" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7432" class="Bound">y</a><a id="7466" class="Symbol">)</a>
<a id="7468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7384" class="Function">to∘from′</a> <a id="7477" class="Symbol">(</a><a id="7478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6936" class="InductiveConstructor">mk-≃′</a> <a id="7484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7484" class="Bound">f</a> <a id="7486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7486" class="Bound">g</a> <a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7488" class="Bound">g∘f</a> <a id="7492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7492" class="Bound">f∘g</a><a id="7495" class="Symbol">)</a> <a id="7497" class="Symbol">=</a> <a id="7499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7492" class="Bound">f∘g</a>{% endraw %}</pre>

{::comment}
We construct values of the record type with the syntax
{:/}

我们用下面的语法来构造一个记录类型的值：

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

这与使用相应的归纳类型的构造器对应：

    mk-≃′ f g g∘f f∘g

{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。


{::comment}
## Isomorphism is an equivalence
{:/}

## 同构是一个等价关系

{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数作为 `to` 和 `from`：

<pre class="Agda">{% raw %}<a id="≃-refl"></a><a id="8305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8305" class="Function">≃-refl</a> <a id="8312" class="Symbol">:</a> <a id="8314" class="Symbol">∀</a> <a id="8316" class="Symbol">{</a><a id="8317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8317" class="Bound">A</a> <a id="8319" class="Symbol">:</a> <a id="8321" class="PrimitiveType">Set</a><a id="8324" class="Symbol">}</a>
    <a id="8330" class="Comment">-----</a>
  <a id="8338" class="Symbol">→</a> <a id="8340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8317" class="Bound">A</a> <a id="8342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="8344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8317" class="Bound">A</a>
<a id="8346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8305" class="Function">≃-refl</a> <a id="8353" class="Symbol">=</a>
  <a id="8357" class="Keyword">record</a>
    <a id="8368" class="Symbol">{</a> <a id="8370" class="Field">to</a>      <a id="8378" class="Symbol">=</a> <a id="8380" class="Symbol">λ{</a><a id="8382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8382" class="Bound">x</a> <a id="8384" class="Symbol">→</a> <a id="8386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8382" class="Bound">x</a><a id="8387" class="Symbol">}</a>
    <a id="8393" class="Symbol">;</a> <a id="8395" class="Field">from</a>    <a id="8403" class="Symbol">=</a> <a id="8405" class="Symbol">λ{</a><a id="8407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8407" class="Bound">y</a> <a id="8409" class="Symbol">→</a> <a id="8411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8407" class="Bound">y</a><a id="8412" class="Symbol">}</a>
    <a id="8418" class="Symbol">;</a> <a id="8420" class="Field">from∘to</a> <a id="8428" class="Symbol">=</a> <a id="8430" class="Symbol">λ{</a><a id="8432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8432" class="Bound">x</a> <a id="8434" class="Symbol">→</a> <a id="8436" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="8440" class="Symbol">}</a>
    <a id="8446" class="Symbol">;</a> <a id="8448" class="Field">to∘from</a> <a id="8456" class="Symbol">=</a> <a id="8458" class="Symbol">λ{</a><a id="8460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8460" class="Bound">y</a> <a id="8462" class="Symbol">→</a> <a id="8464" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="8468" class="Symbol">}</a>
    <a id="8474" class="Symbol">}</a>{% endraw %}</pre>

{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。

{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：

<pre class="Agda">{% raw %}<a id="≃-sym"></a><a id="9144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9144" class="Function">≃-sym</a> <a id="9150" class="Symbol">:</a> <a id="9152" class="Symbol">∀</a> <a id="9154" class="Symbol">{</a><a id="9155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9155" class="Bound">A</a> <a id="9157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9157" class="Bound">B</a> <a id="9159" class="Symbol">:</a> <a id="9161" class="PrimitiveType">Set</a><a id="9164" class="Symbol">}</a>
  <a id="9168" class="Symbol">→</a> <a id="9170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9155" class="Bound">A</a> <a id="9172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="9174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9157" class="Bound">B</a>
    <a id="9180" class="Comment">-----</a>
  <a id="9188" class="Symbol">→</a> <a id="9190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9157" class="Bound">B</a> <a id="9192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="9194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9155" class="Bound">A</a>
<a id="9196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9144" class="Function">≃-sym</a> <a id="9202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9202" class="Bound">A≃B</a> <a id="9206" class="Symbol">=</a>
  <a id="9210" class="Keyword">record</a>
    <a id="9221" class="Symbol">{</a> <a id="9223" class="Field">to</a>      <a id="9231" class="Symbol">=</a> <a id="9233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9202" class="Bound">A≃B</a>
    <a id="9246" class="Symbol">;</a> <a id="9248" class="Field">from</a>    <a id="9256" class="Symbol">=</a> <a id="9258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a>   <a id="9263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9202" class="Bound">A≃B</a>
    <a id="9271" class="Symbol">;</a> <a id="9273" class="Field">from∘to</a> <a id="9281" class="Symbol">=</a> <a id="9283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5677" class="Field">to∘from</a> <a id="9291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9202" class="Bound">A≃B</a>
    <a id="9299" class="Symbol">;</a> <a id="9301" class="Field">to∘from</a> <a id="9309" class="Symbol">=</a> <a id="9311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5635" class="Field">from∘to</a> <a id="9319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9202" class="Bound">A≃B</a>
    <a id="9327" class="Symbol">}</a>{% endraw %}</pre>

{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：

<pre class="Agda">{% raw %}<a id="≃-trans"></a><a id="9557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9557" class="Function">≃-trans</a> <a id="9565" class="Symbol">:</a> <a id="9567" class="Symbol">∀</a> <a id="9569" class="Symbol">{</a><a id="9570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9570" class="Bound">A</a> <a id="9572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9572" class="Bound">B</a> <a id="9574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9574" class="Bound">C</a> <a id="9576" class="Symbol">:</a> <a id="9578" class="PrimitiveType">Set</a><a id="9581" class="Symbol">}</a>
  <a id="9585" class="Symbol">→</a> <a id="9587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9570" class="Bound">A</a> <a id="9589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="9591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9572" class="Bound">B</a>
  <a id="9595" class="Symbol">→</a> <a id="9597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9572" class="Bound">B</a> <a id="9599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="9601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9574" class="Bound">C</a>
    <a id="9607" class="Comment">-----</a>
  <a id="9615" class="Symbol">→</a> <a id="9617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9570" class="Bound">A</a> <a id="9619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="9621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9574" class="Bound">C</a>
<a id="9623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9557" class="Function">≃-trans</a> <a id="9631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9639" class="Symbol">=</a>
  <a id="9643" class="Keyword">record</a>
    <a id="9654" class="Symbol">{</a> <a id="9656" class="Field">to</a>       <a id="9665" class="Symbol">=</a> <a id="9667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a>   <a id="9672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="9678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a>   <a id="9683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a>
    <a id="9691" class="Symbol">;</a> <a id="9693" class="Field">from</a>     <a id="9702" class="Symbol">=</a> <a id="9704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="9715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a>
    <a id="9728" class="Symbol">;</a> <a id="9730" class="Field">from∘to</a>  <a id="9739" class="Symbol">=</a> <a id="9741" class="Symbol">λ{</a><a id="9743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a> <a id="9745" class="Symbol">→</a>
        <a id="9755" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="9771" class="Symbol">(</a><a id="9772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="9783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a><a id="9791" class="Symbol">)</a> <a id="9793" class="Symbol">((</a><a id="9795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="9804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a><a id="9810" class="Symbol">)</a> <a id="9812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a><a id="9813" class="Symbol">)</a>
        <a id="9823" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
          <a id="9837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9846" class="Symbol">(</a><a id="9847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9856" class="Symbol">(</a><a id="9857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9864" class="Symbol">(</a><a id="9865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a><a id="9873" class="Symbol">)))</a>
        <a id="9885" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="9888" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="9893" class="Symbol">(</a><a id="9894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a><a id="9902" class="Symbol">)</a> <a id="9904" class="Symbol">(</a><a id="9905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5635" class="Field">from∘to</a> <a id="9913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="9917" class="Symbol">(</a><a id="9918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a><a id="9926" class="Symbol">))</a> <a id="9929" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="9941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="9946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9950" class="Symbol">(</a><a id="9951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="9954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a><a id="9959" class="Symbol">)</a>
        <a id="9969" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="9972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5635" class="Field">from∘to</a> <a id="9980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="9984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a> <a id="9986" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="9998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9743" class="Bound">x</a>
        <a id="10008" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="10009" class="Symbol">}</a>
    <a id="10015" class="Symbol">;</a> <a id="10017" class="Field">to∘from</a> <a id="10025" class="Symbol">=</a> <a id="10027" class="Symbol">λ{</a><a id="10029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a> <a id="10031" class="Symbol">→</a>
        <a id="10041" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="10057" class="Symbol">(</a><a id="10058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="10067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a><a id="10073" class="Symbol">)</a> <a id="10075" class="Symbol">((</a><a id="10077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="10086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2744" class="Function Operator">∘</a> <a id="10088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a><a id="10096" class="Symbol">)</a> <a id="10098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a><a id="10099" class="Symbol">)</a>
        <a id="10109" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
          <a id="10123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10130" class="Symbol">(</a><a id="10131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="10138" class="Symbol">(</a><a id="10139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="10148" class="Symbol">(</a><a id="10149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a><a id="10159" class="Symbol">)))</a>
        <a id="10171" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="10174" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="10179" class="Symbol">(</a><a id="10180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a><a id="10186" class="Symbol">)</a> <a id="10188" class="Symbol">(</a><a id="10189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5677" class="Field">to∘from</a> <a id="10197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9631" class="Bound">A≃B</a> <a id="10201" class="Symbol">(</a><a id="10202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a><a id="10212" class="Symbol">))</a> <a id="10215" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="10227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5601" class="Field">to</a> <a id="10230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10234" class="Symbol">(</a><a id="10235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5618" class="Field">from</a> <a id="10240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a><a id="10245" class="Symbol">)</a>
        <a id="10255" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="10258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5677" class="Field">to∘from</a> <a id="10266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9635" class="Bound">B≃C</a> <a id="10270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a> <a id="10272" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="10284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10029" class="Bound">y</a>
        <a id="10294" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="10295" class="Symbol">}</a>
     <a id="10302" class="Symbol">}</a>{% endraw %}</pre>


{::comment}
## Equational reasoning for isomorphism
{:/}

## 同构的相等性论证

{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：

<pre class="Agda">{% raw %}<a id="10778" class="Keyword">module</a> <a id="≃-Reasoning"></a><a id="10785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10785" class="Module">≃-Reasoning</a> <a id="10797" class="Keyword">where</a>

  <a id="10806" class="Keyword">infix</a>  <a id="10813" class="Number">1</a> <a id="10815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10861" class="Function Operator">≃-begin_</a>
  <a id="10826" class="Keyword">infixr</a> <a id="10833" class="Number">2</a> <a id="10835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10945" class="Function Operator">_≃⟨_⟩_</a>
  <a id="10844" class="Keyword">infix</a>  <a id="10851" class="Number">3</a> <a id="10853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11064" class="Function Operator">_≃-∎</a>

  <a id="≃-Reasoning.≃-begin_"></a><a id="10861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10861" class="Function Operator">≃-begin_</a> <a id="10870" class="Symbol">:</a> <a id="10872" class="Symbol">∀</a> <a id="10874" class="Symbol">{</a><a id="10875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10875" class="Bound">A</a> <a id="10877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10877" class="Bound">B</a> <a id="10879" class="Symbol">:</a> <a id="10881" class="PrimitiveType">Set</a><a id="10884" class="Symbol">}</a>
    <a id="10890" class="Symbol">→</a> <a id="10892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10875" class="Bound">A</a> <a id="10894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="10896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10877" class="Bound">B</a>
      <a id="10904" class="Comment">-----</a>
    <a id="10914" class="Symbol">→</a> <a id="10916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10875" class="Bound">A</a> <a id="10918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="10920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10877" class="Bound">B</a>
  <a id="10924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10861" class="Function Operator">≃-begin</a> <a id="10932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10932" class="Bound">A≃B</a> <a id="10936" class="Symbol">=</a> <a id="10938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10932" class="Bound">A≃B</a>

  <a id="≃-Reasoning._≃⟨_⟩_"></a><a id="10945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10945" class="Function Operator">_≃⟨_⟩_</a> <a id="10952" class="Symbol">:</a> <a id="10954" class="Symbol">∀</a> <a id="10956" class="Symbol">(</a><a id="10957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10957" class="Bound">A</a> <a id="10959" class="Symbol">:</a> <a id="10961" class="PrimitiveType">Set</a><a id="10964" class="Symbol">)</a> <a id="10966" class="Symbol">{</a><a id="10967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10967" class="Bound">B</a> <a id="10969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10969" class="Bound">C</a> <a id="10971" class="Symbol">:</a> <a id="10973" class="PrimitiveType">Set</a><a id="10976" class="Symbol">}</a>
    <a id="10982" class="Symbol">→</a> <a id="10984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10957" class="Bound">A</a> <a id="10986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="10988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10967" class="Bound">B</a>
    <a id="10994" class="Symbol">→</a> <a id="10996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10967" class="Bound">B</a> <a id="10998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="11000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10969" class="Bound">C</a>
      <a id="11008" class="Comment">-----</a>
    <a id="11018" class="Symbol">→</a> <a id="11020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10957" class="Bound">A</a> <a id="11022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="11024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10969" class="Bound">C</a>
  <a id="11028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11028" class="Bound">A</a> <a id="11030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10945" class="Function Operator">≃⟨</a> <a id="11033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11033" class="Bound">A≃B</a> <a id="11037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10945" class="Function Operator">⟩</a> <a id="11039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11039" class="Bound">B≃C</a> <a id="11043" class="Symbol">=</a> <a id="11045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9557" class="Function">≃-trans</a> <a id="11053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11033" class="Bound">A≃B</a> <a id="11057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11039" class="Bound">B≃C</a>

  <a id="≃-Reasoning._≃-∎"></a><a id="11064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11064" class="Function Operator">_≃-∎</a> <a id="11069" class="Symbol">:</a> <a id="11071" class="Symbol">∀</a> <a id="11073" class="Symbol">(</a><a id="11074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11074" class="Bound">A</a> <a id="11076" class="Symbol">:</a> <a id="11078" class="PrimitiveType">Set</a><a id="11081" class="Symbol">)</a>
      <a id="11089" class="Comment">-----</a>
    <a id="11099" class="Symbol">→</a> <a id="11101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11074" class="Bound">A</a> <a id="11103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="11105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11074" class="Bound">A</a>
  <a id="11109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11109" class="Bound">A</a> <a id="11111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11064" class="Function Operator">≃-∎</a> <a id="11115" class="Symbol">=</a> <a id="11117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8305" class="Function">≃-refl</a>

<a id="11125" class="Keyword">open</a> <a id="11130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10785" class="Module">≃-Reasoning</a>{% endraw %}</pre>


{::comment}
## Embedding
{:/}

## 嵌入（Embedding）

{::comment}
We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.
{:/}

我们同时也需要*嵌入*的概念，它是同构的弱化概念。同构要求证明两个类型之间的一一对应，而嵌入只需要第一种类型涵盖在第二种类型内，所以两个类型之间有一对多的对应关系。

{::comment}
Here is the formal definition of embedding:
{:/}

嵌入的正式定义如下：

<pre class="Agda">{% raw %}<a id="11714" class="Keyword">infix</a> <a id="11720" class="Number">0</a> <a id="11722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">_≲_</a>
<a id="11726" class="Keyword">record</a> <a id="_≲_"></a><a id="11733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">_≲_</a> <a id="11737" class="Symbol">(</a><a id="11738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11738" class="Bound">A</a> <a id="11740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11740" class="Bound">B</a> <a id="11742" class="Symbol">:</a> <a id="11744" class="PrimitiveType">Set</a><a id="11747" class="Symbol">)</a> <a id="11749" class="Symbol">:</a> <a id="11751" class="PrimitiveType">Set</a> <a id="11755" class="Keyword">where</a>
  <a id="11763" class="Keyword">field</a>
    <a id="_≲_.to"></a><a id="11773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a>      <a id="11781" class="Symbol">:</a> <a id="11783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11738" class="Bound">A</a> <a id="11785" class="Symbol">→</a> <a id="11787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11740" class="Bound">B</a>
    <a id="_≲_.from"></a><a id="11793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a>    <a id="11801" class="Symbol">:</a> <a id="11803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11740" class="Bound">B</a> <a id="11805" class="Symbol">→</a> <a id="11807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11738" class="Bound">A</a>
    <a id="_≲_.from∘to"></a><a id="11813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11813" class="Field">from∘to</a> <a id="11821" class="Symbol">:</a> <a id="11823" class="Symbol">∀</a> <a id="11825" class="Symbol">(</a><a id="11826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11826" class="Bound">x</a> <a id="11828" class="Symbol">:</a> <a id="11830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11738" class="Bound">A</a><a id="11831" class="Symbol">)</a> <a id="11833" class="Symbol">→</a> <a id="11835" class="Field">from</a> <a id="11840" class="Symbol">(</a><a id="11841" class="Field">to</a> <a id="11844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11826" class="Bound">x</a><a id="11845" class="Symbol">)</a> <a id="11847" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11826" class="Bound">x</a>
<a id="11851" class="Keyword">open</a> <a id="11856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Module Operator">_≲_</a>{% endraw %}</pre>

{::comment}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.
{:/}

除了它缺少了 `to∘from` 字段以外，嵌入的定义和同构是一样的。因此，我们可以得知 `from` 是 `to`
的左逆，但是 `from` 不是 `to` 的右逆。

{::comment}
Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
{:/}

嵌入是自反和传递的，但不是对称的。证明与同构类似，不过去除了不需要的部分：

<pre class="Agda">{% raw %}<a id="≲-refl"></a><a id="12350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12350" class="Function">≲-refl</a> <a id="12357" class="Symbol">:</a> <a id="12359" class="Symbol">∀</a> <a id="12361" class="Symbol">{</a><a id="12362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12362" class="Bound">A</a> <a id="12364" class="Symbol">:</a> <a id="12366" class="PrimitiveType">Set</a><a id="12369" class="Symbol">}</a> <a id="12371" class="Symbol">→</a> <a id="12373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12362" class="Bound">A</a> <a id="12375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="12377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12362" class="Bound">A</a>
<a id="12379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12350" class="Function">≲-refl</a> <a id="12386" class="Symbol">=</a>
  <a id="12390" class="Keyword">record</a>
    <a id="12401" class="Symbol">{</a> <a id="12403" class="Field">to</a>      <a id="12411" class="Symbol">=</a> <a id="12413" class="Symbol">λ{</a><a id="12415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12415" class="Bound">x</a> <a id="12417" class="Symbol">→</a> <a id="12419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12415" class="Bound">x</a><a id="12420" class="Symbol">}</a>
    <a id="12426" class="Symbol">;</a> <a id="12428" class="Field">from</a>    <a id="12436" class="Symbol">=</a> <a id="12438" class="Symbol">λ{</a><a id="12440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12440" class="Bound">y</a> <a id="12442" class="Symbol">→</a> <a id="12444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12440" class="Bound">y</a><a id="12445" class="Symbol">}</a>
    <a id="12451" class="Symbol">;</a> <a id="12453" class="Field">from∘to</a> <a id="12461" class="Symbol">=</a> <a id="12463" class="Symbol">λ{</a><a id="12465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12465" class="Bound">x</a> <a id="12467" class="Symbol">→</a> <a id="12469" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="12473" class="Symbol">}</a>
    <a id="12479" class="Symbol">}</a>

<a id="≲-trans"></a><a id="12482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12482" class="Function">≲-trans</a> <a id="12490" class="Symbol">:</a> <a id="12492" class="Symbol">∀</a> <a id="12494" class="Symbol">{</a><a id="12495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12495" class="Bound">A</a> <a id="12497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12497" class="Bound">B</a> <a id="12499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12499" class="Bound">C</a> <a id="12501" class="Symbol">:</a> <a id="12503" class="PrimitiveType">Set</a><a id="12506" class="Symbol">}</a> <a id="12508" class="Symbol">→</a> <a id="12510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12495" class="Bound">A</a> <a id="12512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="12514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12497" class="Bound">B</a> <a id="12516" class="Symbol">→</a> <a id="12518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12497" class="Bound">B</a> <a id="12520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="12522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12499" class="Bound">C</a> <a id="12524" class="Symbol">→</a> <a id="12526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12495" class="Bound">A</a> <a id="12528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="12530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12499" class="Bound">C</a>
<a id="12532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12482" class="Function">≲-trans</a> <a id="12540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12548" class="Symbol">=</a>
  <a id="12552" class="Keyword">record</a>
    <a id="12563" class="Symbol">{</a> <a id="12565" class="Field">to</a>      <a id="12573" class="Symbol">=</a> <a id="12575" class="Symbol">λ{</a><a id="12577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12577" class="Bound">x</a> <a id="12579" class="Symbol">→</a> <a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a>   <a id="12586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12590" class="Symbol">(</a><a id="12591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a>   <a id="12596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12577" class="Bound">x</a><a id="12601" class="Symbol">)}</a>
    <a id="12608" class="Symbol">;</a> <a id="12610" class="Field">from</a>    <a id="12618" class="Symbol">=</a> <a id="12620" class="Symbol">λ{</a><a id="12622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12622" class="Bound">y</a> <a id="12624" class="Symbol">→</a> <a id="12626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12635" class="Symbol">(</a><a id="12636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12622" class="Bound">y</a><a id="12646" class="Symbol">)}</a>
    <a id="12653" class="Symbol">;</a> <a id="12655" class="Field">from∘to</a> <a id="12663" class="Symbol">=</a> <a id="12665" class="Symbol">λ{</a><a id="12667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a> <a id="12669" class="Symbol">→</a>
        <a id="12679" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="12695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12704" class="Symbol">(</a><a id="12705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12714" class="Symbol">(</a><a id="12715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="12718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12722" class="Symbol">(</a><a id="12723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="12726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a><a id="12731" class="Symbol">)))</a>
        <a id="12743" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="12746" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="12751" class="Symbol">(</a><a id="12752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a><a id="12760" class="Symbol">)</a> <a id="12762" class="Symbol">(</a><a id="12763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11813" class="Field">from∘to</a> <a id="12771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12544" class="Bound">B≲C</a> <a id="12775" class="Symbol">(</a><a id="12776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="12779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a><a id="12784" class="Symbol">))</a> <a id="12787" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="12799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="12804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12808" class="Symbol">(</a><a id="12809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="12812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a><a id="12817" class="Symbol">)</a>
        <a id="12827" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="12830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11813" class="Field">from∘to</a> <a id="12838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12540" class="Bound">A≲B</a> <a id="12842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a> <a id="12844" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="12856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12667" class="Bound">x</a>
        <a id="12866" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="12867" class="Symbol">}</a>
     <a id="12874" class="Symbol">}</a>{% endraw %}</pre>

{::comment}
It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
{:/}

显而易见的是，如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。这个一种反对称性的弱化形式：

<pre class="Agda">{% raw %}<a id="≲-antisym"></a><a id="13141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13141" class="Function">≲-antisym</a> <a id="13151" class="Symbol">:</a> <a id="13153" class="Symbol">∀</a> <a id="13155" class="Symbol">{</a><a id="13156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13156" class="Bound">A</a> <a id="13158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13158" class="Bound">B</a> <a id="13160" class="Symbol">:</a> <a id="13162" class="PrimitiveType">Set</a><a id="13165" class="Symbol">}</a>
  <a id="13169" class="Symbol">→</a> <a id="13171" class="Symbol">(</a><a id="13172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13172" class="Bound">A≲B</a> <a id="13176" class="Symbol">:</a> <a id="13178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13156" class="Bound">A</a> <a id="13180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="13182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13158" class="Bound">B</a><a id="13183" class="Symbol">)</a>
  <a id="13187" class="Symbol">→</a> <a id="13189" class="Symbol">(</a><a id="13190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13190" class="Bound">B≲A</a> <a id="13194" class="Symbol">:</a> <a id="13196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13158" class="Bound">B</a> <a id="13198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="13200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13156" class="Bound">A</a><a id="13201" class="Symbol">)</a>
  <a id="13205" class="Symbol">→</a> <a id="13207" class="Symbol">(</a><a id="13208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13172" class="Bound">A≲B</a> <a id="13215" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="13222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13190" class="Bound">B≲A</a><a id="13225" class="Symbol">)</a>
  <a id="13229" class="Symbol">→</a> <a id="13231" class="Symbol">(</a><a id="13232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="13237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13172" class="Bound">A≲B</a> <a id="13241" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13190" class="Bound">B≲A</a><a id="13249" class="Symbol">)</a>
    <a id="13255" class="Comment">-------------------</a>
  <a id="13277" class="Symbol">→</a> <a id="13279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13156" class="Bound">A</a> <a id="13281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="13283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13158" class="Bound">B</a>
<a id="13285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13141" class="Function">≲-antisym</a> <a id="13295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a> <a id="13299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13303" class="Bound">to≡from</a> <a id="13311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13311" class="Bound">from≡to</a> <a id="13319" class="Symbol">=</a>
  <a id="13323" class="Keyword">record</a>
    <a id="13334" class="Symbol">{</a> <a id="13336" class="Field">to</a>      <a id="13344" class="Symbol">=</a> <a id="13346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a>
    <a id="13357" class="Symbol">;</a> <a id="13359" class="Field">from</a>    <a id="13367" class="Symbol">=</a> <a id="13369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="13374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a>
    <a id="13382" class="Symbol">;</a> <a id="13384" class="Field">from∘to</a> <a id="13392" class="Symbol">=</a> <a id="13394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11813" class="Field">from∘to</a> <a id="13402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a>
    <a id="13410" class="Symbol">;</a> <a id="13412" class="Field">to∘from</a> <a id="13420" class="Symbol">=</a> <a id="13422" class="Symbol">λ{</a><a id="13424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a> <a id="13426" class="Symbol">→</a>
        <a id="13436" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
          <a id="13452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a> <a id="13459" class="Symbol">(</a><a id="13460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="13465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a> <a id="13469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a><a id="13470" class="Symbol">)</a>
        <a id="13480" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13483" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="13488" class="Symbol">(</a><a id="13489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a><a id="13495" class="Symbol">)</a> <a id="13497" class="Symbol">(</a><a id="13498" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a> <a id="13507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13311" class="Bound">from≡to</a> <a id="13515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a><a id="13516" class="Symbol">)</a> <a id="13518" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Bound">A≲B</a> <a id="13537" class="Symbol">(</a><a id="13538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a><a id="13546" class="Symbol">)</a>
        <a id="13556" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13559" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1274" class="Function">cong-app</a> <a id="13568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13303" class="Bound">to≡from</a> <a id="13576" class="Symbol">(</a><a id="13577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a><a id="13585" class="Symbol">)</a> <a id="13587" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11793" class="Field">from</a> <a id="13604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13608" class="Symbol">(</a><a id="13609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11773" class="Field">to</a> <a id="13612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a><a id="13617" class="Symbol">)</a>
        <a id="13627" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11813" class="Field">from∘to</a> <a id="13638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13299" class="Bound">B≲A</a> <a id="13642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a> <a id="13644" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
          <a id="13656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13424" class="Bound">y</a>
        <a id="13666" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a><a id="13667" class="Symbol">}</a>
    <a id="13673" class="Symbol">}</a>{% endraw %}</pre>

{::comment}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.
{:/}

前三部分可以直接从嵌入中得来，最后一部分我们可以把 `B ≲ A` 中的左逆和两个嵌入中的 `to` 与 `from` 部分的相等性来获得同构中的右逆。


{::comment}
## Equational reasoning for embedding
{:/}

## 嵌入的相等性论证

{::comment}
We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:
{:/}

和同构类似，我们亦支持嵌入的相等性论证：

<pre class="Agda">{% raw %}<a id="14238" class="Keyword">module</a> <a id="≲-Reasoning"></a><a id="14245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14245" class="Module">≲-Reasoning</a> <a id="14257" class="Keyword">where</a>

  <a id="14266" class="Keyword">infix</a>  <a id="14273" class="Number">1</a> <a id="14275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14321" class="Function Operator">≲-begin_</a>
  <a id="14286" class="Keyword">infixr</a> <a id="14293" class="Number">2</a> <a id="14295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14405" class="Function Operator">_≲⟨_⟩_</a>
  <a id="14304" class="Keyword">infix</a>  <a id="14311" class="Number">3</a> <a id="14313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14524" class="Function Operator">_≲-∎</a>

  <a id="≲-Reasoning.≲-begin_"></a><a id="14321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14321" class="Function Operator">≲-begin_</a> <a id="14330" class="Symbol">:</a> <a id="14332" class="Symbol">∀</a> <a id="14334" class="Symbol">{</a><a id="14335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14335" class="Bound">A</a> <a id="14337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14337" class="Bound">B</a> <a id="14339" class="Symbol">:</a> <a id="14341" class="PrimitiveType">Set</a><a id="14344" class="Symbol">}</a>
    <a id="14350" class="Symbol">→</a> <a id="14352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14335" class="Bound">A</a> <a id="14354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14337" class="Bound">B</a>
      <a id="14364" class="Comment">-----</a>
    <a id="14374" class="Symbol">→</a> <a id="14376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14335" class="Bound">A</a> <a id="14378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14337" class="Bound">B</a>
  <a id="14384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14321" class="Function Operator">≲-begin</a> <a id="14392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14392" class="Bound">A≲B</a> <a id="14396" class="Symbol">=</a> <a id="14398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14392" class="Bound">A≲B</a>

  <a id="≲-Reasoning._≲⟨_⟩_"></a><a id="14405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14405" class="Function Operator">_≲⟨_⟩_</a> <a id="14412" class="Symbol">:</a> <a id="14414" class="Symbol">∀</a> <a id="14416" class="Symbol">(</a><a id="14417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14417" class="Bound">A</a> <a id="14419" class="Symbol">:</a> <a id="14421" class="PrimitiveType">Set</a><a id="14424" class="Symbol">)</a> <a id="14426" class="Symbol">{</a><a id="14427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14427" class="Bound">B</a> <a id="14429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14429" class="Bound">C</a> <a id="14431" class="Symbol">:</a> <a id="14433" class="PrimitiveType">Set</a><a id="14436" class="Symbol">}</a>
    <a id="14442" class="Symbol">→</a> <a id="14444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14417" class="Bound">A</a> <a id="14446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14427" class="Bound">B</a>
    <a id="14454" class="Symbol">→</a> <a id="14456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14427" class="Bound">B</a> <a id="14458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14429" class="Bound">C</a>
      <a id="14468" class="Comment">-----</a>
    <a id="14478" class="Symbol">→</a> <a id="14480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14417" class="Bound">A</a> <a id="14482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14429" class="Bound">C</a>
  <a id="14488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14488" class="Bound">A</a> <a id="14490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14405" class="Function Operator">≲⟨</a> <a id="14493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14493" class="Bound">A≲B</a> <a id="14497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14405" class="Function Operator">⟩</a> <a id="14499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14499" class="Bound">B≲C</a> <a id="14503" class="Symbol">=</a> <a id="14505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12482" class="Function">≲-trans</a> <a id="14513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14493" class="Bound">A≲B</a> <a id="14517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14499" class="Bound">B≲C</a>

  <a id="≲-Reasoning._≲-∎"></a><a id="14524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14524" class="Function Operator">_≲-∎</a> <a id="14529" class="Symbol">:</a> <a id="14531" class="Symbol">∀</a> <a id="14533" class="Symbol">(</a><a id="14534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14534" class="Bound">A</a> <a id="14536" class="Symbol">:</a> <a id="14538" class="PrimitiveType">Set</a><a id="14541" class="Symbol">)</a>
      <a id="14549" class="Comment">-----</a>
    <a id="14559" class="Symbol">→</a> <a id="14561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14534" class="Bound">A</a> <a id="14563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14534" class="Bound">A</a>
  <a id="14569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14569" class="Bound">A</a> <a id="14571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14524" class="Function Operator">≲-∎</a> <a id="14575" class="Symbol">=</a> <a id="14577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12350" class="Function">≲-refl</a>

<a id="14585" class="Keyword">open</a> <a id="14590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14245" class="Module">≲-Reasoning</a>{% endraw %}</pre>

{::comment}
#### Exercise `≃-implies-≲`
{:/}

#### 练习 `≃-implies-≲`

{::comment}
Show that every isomorphism implies an embedding.
{:/}

证明每个同构蕴含了一个嵌入。

<pre class="Agda">{% raw %}<a id="14780" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="14792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14792" class="Postulate">≃-implies-≲</a> <a id="14804" class="Symbol">:</a> <a id="14806" class="Symbol">∀</a> <a id="14808" class="Symbol">{</a><a id="14809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14809" class="Bound">A</a> <a id="14811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14811" class="Bound">B</a> <a id="14813" class="Symbol">:</a> <a id="14815" class="PrimitiveType">Set</a><a id="14818" class="Symbol">}</a>
    <a id="14824" class="Symbol">→</a> <a id="14826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14809" class="Bound">A</a> <a id="14828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5561" class="Record Operator">≃</a> <a id="14830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14811" class="Bound">B</a>
      <a id="14838" class="Comment">-----</a>
    <a id="14848" class="Symbol">→</a> <a id="14850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14809" class="Bound">A</a> <a id="14852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11733" class="Record Operator">≲</a> <a id="14854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14811" class="Bound">B</a>{% endraw %}</pre>

{::comment}
<pre class="Agda">{% raw %}<a id="14893" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="14946" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `_⇔_` {#iff}
{:/}

#### 练习 `_⇔_` {#iff}

{::comment}
Define equivalence of propositions (also known as "if and only if") as follows:
{:/}

按下列形式定义命题的等价性（又名“当且仅当“）：

<pre class="Agda">{% raw %}<a id="15175" class="Keyword">record</a> <a id="_⇔_"></a><a id="15182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15182" class="Record Operator">_⇔_</a> <a id="15186" class="Symbol">(</a><a id="15187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15187" class="Bound">A</a> <a id="15189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15189" class="Bound">B</a> <a id="15191" class="Symbol">:</a> <a id="15193" class="PrimitiveType">Set</a><a id="15196" class="Symbol">)</a> <a id="15198" class="Symbol">:</a> <a id="15200" class="PrimitiveType">Set</a> <a id="15204" class="Keyword">where</a>
  <a id="15212" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="15222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15222" class="Field">to</a>   <a id="15227" class="Symbol">:</a> <a id="15229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15187" class="Bound">A</a> <a id="15231" class="Symbol">→</a> <a id="15233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15189" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="15239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15239" class="Field">from</a> <a id="15244" class="Symbol">:</a> <a id="15246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15189" class="Bound">B</a> <a id="15248" class="Symbol">→</a> <a id="15250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15187" class="Bound">A</a>{% endraw %}</pre>

{::comment}
Show that equivalence is reflexive, symmetric, and transitive.
{:/}

证明等价性是自反、对称和传递的。

{::comment}
<pre class="Agda">{% raw %}<a id="15388" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="15441" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}
{:/}

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) and
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws)
define a datatype of bitstrings representing natural numbers:
{:/}

回忆练习 [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) 和 
[Bin-laws]({{ site.baseurl }}{% link out/plfa/Induction.md%}#Bin-laws) 中，我们定义了一个数据类型来表示二进制比特串来表示自然数：

<pre class="Agda">{% raw %}<a id="15869" class="Keyword">data</a> <a id="Bin"></a><a id="15874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a> <a id="15878" class="Symbol">:</a> <a id="15880" class="PrimitiveType">Set</a> <a id="15884" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="15892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15892" class="InductiveConstructor">nil</a> <a id="15896" class="Symbol">:</a> <a id="15898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="15904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15904" class="InductiveConstructor Operator">x0_</a> <a id="15908" class="Symbol">:</a> <a id="15910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a> <a id="15914" class="Symbol">→</a> <a id="15916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="15922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15922" class="InductiveConstructor Operator">x1_</a> <a id="15926" class="Symbol">:</a> <a id="15928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a> <a id="15932" class="Symbol">→</a> <a id="15934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15874" class="Datatype">Bin</a>{% endraw %}</pre>

{::comment}
And ask you to define the following functions
{:/}

我们要求你来定义下列函数：

    to : ℕ → Bin
    from : Bin → ℕ

{::comment}
which satisfy the following property:
{:/}

其满足如下性质：

    from (to n) ≡ n

{::comment}
Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{:/}

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。

{::comment}
<pre class="Agda">{% raw %}<a id="16302" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="16355" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
Why do `to` and `from` not form an isomorphism?
{:/}

为什么 `to` 和 `from` 不能构造一个同构？


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

<pre class="Agda">{% raw %}<a id="16657" class="Keyword">import</a> <a id="16664" href="https://agda.github.io/agda-stdlib/v0.17/Function.html" class="Module">Function</a> <a id="16673" class="Keyword">using</a> <a id="16679" class="Symbol">(</a><a id="16680" href="https://agda.github.io/agda-stdlib/v0.17/Function.html#769" class="Function Operator">_∘_</a><a id="16683" class="Symbol">)</a>
<a id="16685" class="Keyword">import</a> <a id="16692" href="https://agda.github.io/agda-stdlib/v0.17/Function.Inverse.html" class="Module">Function.Inverse</a> <a id="16709" class="Keyword">using</a> <a id="16715" class="Symbol">(</a><a id="16716" href="https://agda.github.io/agda-stdlib/v0.17/Function.Inverse.html#2193" class="Function Operator">_↔_</a><a id="16719" class="Symbol">)</a>
<a id="16721" class="Keyword">import</a> <a id="16728" href="https://agda.github.io/agda-stdlib/v0.17/Function.LeftInverse.html" class="Module">Function.LeftInverse</a> <a id="16749" class="Keyword">using</a> <a id="16755" class="Symbol">(</a><a id="16756" href="https://agda.github.io/agda-stdlib/v0.17/Function.LeftInverse.html#2641" class="Function Operator">_↞_</a><a id="16759" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.
{:/}

标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，并可以由任何相等性的记法来参数化。


## Unicode
{::comment}
This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用了如下 Unicode：

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
