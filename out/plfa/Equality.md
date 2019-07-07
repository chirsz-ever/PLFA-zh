---
src       : src/plfa/Equality.lagda
title     : "Equality: 相等性与等式推理"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
translators : ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="192" class="Keyword">module</a> <a id="199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="213" class="Keyword">where</a>{% endraw %}</pre>

{::comment}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
{:/}

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，我们将相等性作为一个基础运算，而现在我们来说明如果将其定义为一个归纳的数据类型。


{::comment}
## Imports
{:/}

## 导入

{::comment}
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
{:/}

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。我们在此定义相等性，导入其他内容将会产生冲突。


{::comment}
## Equality
{:/}

## 相等性

{::comment}
We declare equality as follows:
{:/}

我们如下定义相等性：

<pre class="Agda">{% raw %}<a id="1073" class="Keyword">data</a> <a id="_≡_"></a><a id="1078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">_≡_</a> <a id="1082" class="Symbol">{</a><a id="1083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1083" class="Bound">A</a> <a id="1085" class="Symbol">:</a> <a id="1087" class="PrimitiveType">Set</a><a id="1090" class="Symbol">}</a> <a id="1092" class="Symbol">(</a><a id="1093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1093" class="Bound">x</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1083" class="Bound">A</a><a id="1098" class="Symbol">)</a> <a id="1100" class="Symbol">:</a> <a id="1102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1083" class="Bound">A</a> <a id="1104" class="Symbol">→</a> <a id="1106" class="PrimitiveType">Set</a> <a id="1110" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="1118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="1123" class="Symbol">:</a> <a id="1125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1093" class="Bound">x</a> <a id="1127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="1129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1093" class="Bound">x</a>{% endraw %}</pre>

{::comment}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
{:/}

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造器 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，而第二个参数（Argument）则是由 `A → Set` 的索引给出。这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，这样它才可以等用于第一个。

{::comment}
We declare the precedence of equality as follows:
{:/}

我们如下定义相等性的优先级：

<pre class="Agda">{% raw %}<a id="2147" class="Keyword">infix</a> <a id="2153" class="Number">4</a> <a id="2155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">_≡_</a>{% endraw %}</pre>

{::comment}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
{:/}

我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以其它算术运算符的结合都比它紧密。由于它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。


{::comment}
## Equality is an equivalence relation
{:/}

## 相等性是一个等价关系（Equivalence Relation）

{::comment}
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{:/}

一个等价关系是自反、对称和传递的。其中自反性可以通过构造器 `refl` 直接从相等性的定义中得来。我们可以直接地证明其对称性：

<pre class="Agda">{% raw %}<a id="sym"></a><a id="2874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2874" class="Function">sym</a> <a id="2878" class="Symbol">:</a> <a id="2880" class="Symbol">∀</a> <a id="2882" class="Symbol">{</a><a id="2883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2883" class="Bound">A</a> <a id="2885" class="Symbol">:</a> <a id="2887" class="PrimitiveType">Set</a><a id="2890" class="Symbol">}</a> <a id="2892" class="Symbol">{</a><a id="2893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2893" class="Bound">x</a> <a id="2895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2895" class="Bound">y</a> <a id="2897" class="Symbol">:</a> <a id="2899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2883" class="Bound">A</a><a id="2900" class="Symbol">}</a>
  <a id="2904" class="Symbol">→</a> <a id="2906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2893" class="Bound">x</a> <a id="2908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="2910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2895" class="Bound">y</a>
    <a id="2916" class="Comment">-----</a>
  <a id="2924" class="Symbol">→</a> <a id="2926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2895" class="Bound">y</a> <a id="2928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="2930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2893" class="Bound">x</a>
<a id="2932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2874" class="Function">sym</a> <a id="2936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="2941" class="Symbol">=</a> <a id="2943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
{:/}

这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。

{::comment}
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
{:/}

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

{::comment}
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
{:/}

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为其所有可能的构造器。此处只有一个构造器：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

{::comment}
This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
{:/}

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。

{::comment}
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
{:/}

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造器实例。

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

{::comment}
This completes the definition as given above.
{:/}

我们至此完成了与之前给出证明相同的证明。

{::comment}
Transitivity is equally straightforward:
{:/}

传递性亦是很直接：

<pre class="Agda">{% raw %}<a id="trans"></a><a id="5228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5228" class="Function">trans</a> <a id="5234" class="Symbol">:</a> <a id="5236" class="Symbol">∀</a> <a id="5238" class="Symbol">{</a><a id="5239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5239" class="Bound">A</a> <a id="5241" class="Symbol">:</a> <a id="5243" class="PrimitiveType">Set</a><a id="5246" class="Symbol">}</a> <a id="5248" class="Symbol">{</a><a id="5249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5249" class="Bound">x</a> <a id="5251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5251" class="Bound">y</a> <a id="5253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5253" class="Bound">z</a> <a id="5255" class="Symbol">:</a> <a id="5257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5239" class="Bound">A</a><a id="5258" class="Symbol">}</a>
  <a id="5262" class="Symbol">→</a> <a id="5264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5249" class="Bound">x</a> <a id="5266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="5268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5251" class="Bound">y</a>
  <a id="5272" class="Symbol">→</a> <a id="5274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5251" class="Bound">y</a> <a id="5276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="5278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5253" class="Bound">z</a>
    <a id="5284" class="Comment">-----</a>
  <a id="5292" class="Symbol">→</a> <a id="5294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5249" class="Bound">x</a> <a id="5296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="5298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5253" class="Bound">z</a>
<a id="5300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5228" class="Function">trans</a> <a id="5306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="5311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>  <a id="5317" class="Symbol">=</a>  <a id="5320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
{:/}

同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。


{::comment}
## Congruence and substitution {#cong}
{:/}

## 合同性和替换性 {#cong}

{::comment}
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{:/}

相等性满足 *合同性*（Congurence）。如果两个项相等，那么对它们使用相同的函数，其结果仍然相等：

<pre class="Agda">{% raw %}<a id="cong"></a><a id="5844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Function">cong</a> <a id="5849" class="Symbol">:</a> <a id="5851" class="Symbol">∀</a> <a id="5853" class="Symbol">{</a><a id="5854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5854" class="Bound">A</a> <a id="5856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5856" class="Bound">B</a> <a id="5858" class="Symbol">:</a> <a id="5860" class="PrimitiveType">Set</a><a id="5863" class="Symbol">}</a> <a id="5865" class="Symbol">(</a><a id="5866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5866" class="Bound">f</a> <a id="5868" class="Symbol">:</a> <a id="5870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5854" class="Bound">A</a> <a id="5872" class="Symbol">→</a> <a id="5874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5856" class="Bound">B</a><a id="5875" class="Symbol">)</a> <a id="5877" class="Symbol">{</a><a id="5878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5878" class="Bound">x</a> <a id="5880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5880" class="Bound">y</a> <a id="5882" class="Symbol">:</a> <a id="5884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5854" class="Bound">A</a><a id="5885" class="Symbol">}</a>
  <a id="5889" class="Symbol">→</a> <a id="5891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5878" class="Bound">x</a> <a id="5893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="5895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5880" class="Bound">y</a>
    <a id="5901" class="Comment">---------</a>
  <a id="5913" class="Symbol">→</a> <a id="5915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5866" class="Bound">f</a> <a id="5917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5878" class="Bound">x</a> <a id="5919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="5921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5866" class="Bound">f</a> <a id="5923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5880" class="Bound">y</a>
<a id="5925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Function">cong</a> <a id="5930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5930" class="Bound">f</a> <a id="5932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>  <a id="5938" class="Symbol">=</a>  <a id="5941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
Congruence of functions with two arguments is similar:
{:/}

两个参数的函数也满足合同性：

<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="6060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6060" class="Function">cong₂</a> <a id="6066" class="Symbol">:</a> <a id="6068" class="Symbol">∀</a> <a id="6070" class="Symbol">{</a><a id="6071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6071" class="Bound">A</a> <a id="6073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6073" class="Bound">B</a> <a id="6075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6075" class="Bound">C</a> <a id="6077" class="Symbol">:</a> <a id="6079" class="PrimitiveType">Set</a><a id="6082" class="Symbol">}</a> <a id="6084" class="Symbol">(</a><a id="6085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6085" class="Bound">f</a> <a id="6087" class="Symbol">:</a> <a id="6089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6071" class="Bound">A</a> <a id="6091" class="Symbol">→</a> <a id="6093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6073" class="Bound">B</a> <a id="6095" class="Symbol">→</a> <a id="6097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6075" class="Bound">C</a><a id="6098" class="Symbol">)</a> <a id="6100" class="Symbol">{</a><a id="6101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6101" class="Bound">u</a> <a id="6103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6103" class="Bound">x</a> <a id="6105" class="Symbol">:</a> <a id="6107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6071" class="Bound">A</a><a id="6108" class="Symbol">}</a> <a id="6110" class="Symbol">{</a><a id="6111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6111" class="Bound">v</a> <a id="6113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6113" class="Bound">y</a> <a id="6115" class="Symbol">:</a> <a id="6117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6073" class="Bound">B</a><a id="6118" class="Symbol">}</a>
  <a id="6122" class="Symbol">→</a> <a id="6124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6101" class="Bound">u</a> <a id="6126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6103" class="Bound">x</a>
  <a id="6132" class="Symbol">→</a> <a id="6134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6111" class="Bound">v</a> <a id="6136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6113" class="Bound">y</a>
    <a id="6144" class="Comment">-------------</a>
  <a id="6160" class="Symbol">→</a> <a id="6162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6085" class="Bound">f</a> <a id="6164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6101" class="Bound">u</a> <a id="6166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6111" class="Bound">v</a> <a id="6168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6085" class="Bound">f</a> <a id="6172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6103" class="Bound">x</a> <a id="6174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6113" class="Bound">y</a>
<a id="6176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6060" class="Function">cong₂</a> <a id="6182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6182" class="Bound">f</a> <a id="6184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="6189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>  <a id="6195" class="Symbol">=</a>  <a id="6198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{:/}

在函数上的等价性也满足合同性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：

<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="6451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6451" class="Function">cong-app</a> <a id="6460" class="Symbol">:</a> <a id="6462" class="Symbol">∀</a> <a id="6464" class="Symbol">{</a><a id="6465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6465" class="Bound">A</a> <a id="6467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6467" class="Bound">B</a> <a id="6469" class="Symbol">:</a> <a id="6471" class="PrimitiveType">Set</a><a id="6474" class="Symbol">}</a> <a id="6476" class="Symbol">{</a><a id="6477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6477" class="Bound">f</a> <a id="6479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6479" class="Bound">g</a> <a id="6481" class="Symbol">:</a> <a id="6483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6465" class="Bound">A</a> <a id="6485" class="Symbol">→</a> <a id="6487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6467" class="Bound">B</a><a id="6488" class="Symbol">}</a>
  <a id="6492" class="Symbol">→</a> <a id="6494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6477" class="Bound">f</a> <a id="6496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6479" class="Bound">g</a>
    <a id="6504" class="Comment">---------------------</a>
  <a id="6528" class="Symbol">→</a> <a id="6530" class="Symbol">∀</a> <a id="6532" class="Symbol">(</a><a id="6533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6533" class="Bound">x</a> <a id="6535" class="Symbol">:</a> <a id="6537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6465" class="Bound">A</a><a id="6538" class="Symbol">)</a> <a id="6540" class="Symbol">→</a> <a id="6542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6477" class="Bound">f</a> <a id="6544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6533" class="Bound">x</a> <a id="6546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6479" class="Bound">g</a> <a id="6550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6533" class="Bound">x</a>
<a id="6552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6451" class="Function">cong-app</a> <a id="6561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="6566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6566" class="Bound">x</a> <a id="6568" class="Symbol">=</a> <a id="6570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{:/}

相等性也满足*替换性*（Substitution）。如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。

<pre class="Agda">{% raw %}<a id="subst"></a><a id="6810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6810" class="Function">subst</a> <a id="6816" class="Symbol">:</a> <a id="6818" class="Symbol">∀</a> <a id="6820" class="Symbol">{</a><a id="6821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6821" class="Bound">A</a> <a id="6823" class="Symbol">:</a> <a id="6825" class="PrimitiveType">Set</a><a id="6828" class="Symbol">}</a> <a id="6830" class="Symbol">{</a><a id="6831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6831" class="Bound">x</a> <a id="6833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6833" class="Bound">y</a> <a id="6835" class="Symbol">:</a> <a id="6837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6821" class="Bound">A</a><a id="6838" class="Symbol">}</a> <a id="6840" class="Symbol">(</a><a id="6841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6841" class="Bound">P</a> <a id="6843" class="Symbol">:</a> <a id="6845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6821" class="Bound">A</a> <a id="6847" class="Symbol">→</a> <a id="6849" class="PrimitiveType">Set</a><a id="6852" class="Symbol">)</a>
  <a id="6856" class="Symbol">→</a> <a id="6858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6831" class="Bound">x</a> <a id="6860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="6862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6833" class="Bound">y</a>
    <a id="6868" class="Comment">---------</a>
  <a id="6880" class="Symbol">→</a> <a id="6882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6841" class="Bound">P</a> <a id="6884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6831" class="Bound">x</a> <a id="6886" class="Symbol">→</a> <a id="6888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6841" class="Bound">P</a> <a id="6890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6833" class="Bound">y</a>
<a id="6892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6810" class="Function">subst</a> <a id="6898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6898" class="Bound">P</a> <a id="6900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a> <a id="6905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6905" class="Bound">px</a> <a id="6908" class="Symbol">=</a> <a id="6910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6905" class="Bound">px</a>{% endraw %}</pre>


{::comment}
## Chains of equations
{:/}

## 等式串

{::comment}
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{:/}

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们讲声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。

<pre class="Agda">{% raw %}<a id="7297" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="7304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7304" class="Module">≡-Reasoning</a> <a id="7316" class="Symbol">{</a><a id="7317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a> <a id="7319" class="Symbol">:</a> <a id="7321" class="PrimitiveType">Set</a><a id="7324" class="Symbol">}</a> <a id="7326" class="Keyword">where</a>

  <a id="7335" class="Keyword">infix</a>  <a id="7342" class="Number">1</a> <a id="7344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin_</a>
  <a id="7353" class="Keyword">infixr</a> <a id="7360" class="Number">2</a> <a id="7362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7472" class="Function Operator">_≡⟨⟩_</a> <a id="7368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">_≡⟨_⟩_</a>
  <a id="7377" class="Keyword">infix</a>  <a id="7384" class="Number">3</a> <a id="7386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="7392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin_</a> <a id="7399" class="Symbol">:</a> <a id="7401" class="Symbol">∀</a> <a id="7403" class="Symbol">{</a><a id="7404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Bound">x</a> <a id="7406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7406" class="Bound">y</a> <a id="7408" class="Symbol">:</a> <a id="7410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7411" class="Symbol">}</a>
    <a id="7417" class="Symbol">→</a> <a id="7419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Bound">x</a> <a id="7421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7406" class="Bound">y</a>
      <a id="7431" class="Comment">-----</a>
    <a id="7441" class="Symbol">→</a> <a id="7443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Bound">x</a> <a id="7445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7406" class="Bound">y</a>
  <a id="7451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin</a> <a id="7457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7457" class="Bound">x≡y</a>  <a id="7462" class="Symbol">=</a>  <a id="7465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7457" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="7472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7472" class="Function Operator">_≡⟨⟩_</a> <a id="7478" class="Symbol">:</a> <a id="7480" class="Symbol">∀</a> <a id="7482" class="Symbol">(</a><a id="7483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7483" class="Bound">x</a> <a id="7485" class="Symbol">:</a> <a id="7487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7488" class="Symbol">)</a> <a id="7490" class="Symbol">{</a><a id="7491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7491" class="Bound">y</a> <a id="7493" class="Symbol">:</a> <a id="7495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7496" class="Symbol">}</a>
    <a id="7502" class="Symbol">→</a> <a id="7504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7483" class="Bound">x</a> <a id="7506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7491" class="Bound">y</a>
      <a id="7516" class="Comment">-----</a>
    <a id="7526" class="Symbol">→</a> <a id="7528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7483" class="Bound">x</a> <a id="7530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7491" class="Bound">y</a>
  <a id="7536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7536" class="Bound">x</a> <a id="7538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7472" class="Function Operator">≡⟨⟩</a> <a id="7542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7542" class="Bound">x≡y</a>  <a id="7547" class="Symbol">=</a>  <a id="7550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7542" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="7557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">_≡⟨_⟩_</a> <a id="7564" class="Symbol">:</a> <a id="7566" class="Symbol">∀</a> <a id="7568" class="Symbol">(</a><a id="7569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7569" class="Bound">x</a> <a id="7571" class="Symbol">:</a> <a id="7573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7574" class="Symbol">)</a> <a id="7576" class="Symbol">{</a><a id="7577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7577" class="Bound">y</a> <a id="7579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7579" class="Bound">z</a> <a id="7581" class="Symbol">:</a> <a id="7583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7584" class="Symbol">}</a>
    <a id="7590" class="Symbol">→</a> <a id="7592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7569" class="Bound">x</a> <a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7577" class="Bound">y</a>
    <a id="7602" class="Symbol">→</a> <a id="7604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7577" class="Bound">y</a> <a id="7606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7579" class="Bound">z</a>
      <a id="7616" class="Comment">-----</a>
    <a id="7626" class="Symbol">→</a> <a id="7628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7569" class="Bound">x</a> <a id="7630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7579" class="Bound">z</a>
  <a id="7636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7636" class="Bound">x</a> <a id="7638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="7641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7641" class="Bound">x≡y</a> <a id="7645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a> <a id="7647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7647" class="Bound">y≡z</a>  <a id="7652" class="Symbol">=</a>  <a id="7655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5228" class="Function">trans</a> <a id="7661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7641" class="Bound">x≡y</a> <a id="7665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7647" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="7672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">_∎</a> <a id="7675" class="Symbol">:</a> <a id="7677" class="Symbol">∀</a> <a id="7679" class="Symbol">(</a><a id="7680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7680" class="Bound">x</a> <a id="7682" class="Symbol">:</a> <a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7317" class="Bound">A</a><a id="7685" class="Symbol">)</a>
      <a id="7693" class="Comment">-----</a>
    <a id="7703" class="Symbol">→</a> <a id="7705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7680" class="Bound">x</a> <a id="7707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="7709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7680" class="Bound">x</a>
  <a id="7713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7713" class="Bound">x</a> <a id="7715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">∎</a>  <a id="7718" class="Symbol">=</a>  <a id="7721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>

<a id="7727" class="Keyword">open</a> <a id="7732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7304" class="Module">≡-Reasoning</a>{% endraw %}</pre>

{::comment}
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
{:/}

这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。打开（Open）一个模块会把模块内的所有定义导入进当前的环境中。

{::comment}
As an example, let's look at a proof of transitivity
as a chain of equations:
{:/}

举个例子，我们来看看如何用等式串证明传递性：

<pre class="Agda">{% raw %}<a id="trans′"></a><a id="8609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8609" class="Function">trans′</a> <a id="8616" class="Symbol">:</a> <a id="8618" class="Symbol">∀</a> <a id="8620" class="Symbol">{</a><a id="8621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8621" class="Bound">A</a> <a id="8623" class="Symbol">:</a> <a id="8625" class="PrimitiveType">Set</a><a id="8628" class="Symbol">}</a> <a id="8630" class="Symbol">{</a><a id="8631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8631" class="Bound">x</a> <a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8633" class="Bound">y</a> <a id="8635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8635" class="Bound">z</a> <a id="8637" class="Symbol">:</a> <a id="8639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8621" class="Bound">A</a><a id="8640" class="Symbol">}</a>
  <a id="8644" class="Symbol">→</a> <a id="8646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8631" class="Bound">x</a> <a id="8648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="8650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8633" class="Bound">y</a>
  <a id="8654" class="Symbol">→</a> <a id="8656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8633" class="Bound">y</a> <a id="8658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="8660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8635" class="Bound">z</a>
    <a id="8666" class="Comment">-----</a>
  <a id="8674" class="Symbol">→</a> <a id="8676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8631" class="Bound">x</a> <a id="8678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="8680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8635" class="Bound">z</a>
<a id="8682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8609" class="Function">trans′</a> <a id="8689" class="Symbol">{</a><a id="8690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8690" class="Bound">A</a><a id="8691" class="Symbol">}</a> <a id="8693" class="Symbol">{</a><a id="8694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8694" class="Bound">x</a><a id="8695" class="Symbol">}</a> <a id="8697" class="Symbol">{</a><a id="8698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8698" class="Bound">y</a><a id="8699" class="Symbol">}</a> <a id="8701" class="Symbol">{</a><a id="8702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8702" class="Bound">z</a><a id="8703" class="Symbol">}</a> <a id="8705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8705" class="Bound">x≡y</a> <a id="8709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8709" class="Bound">y≡z</a> <a id="8713" class="Symbol">=</a>
  <a id="8717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin</a>
    <a id="8727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8694" class="Bound">x</a>
  <a id="8731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="8734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8705" class="Bound">x≡y</a> <a id="8738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a>
    <a id="8744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8698" class="Bound">y</a>
  <a id="8748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="8751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8709" class="Bound">y≡z</a> <a id="8755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a>
    <a id="8761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8702" class="Bound">z</a>
  <a id="8765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
According to the fixity declarations, the body parses as follows:
{:/}

根据其定义，等式右边会被解析成如下：

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

{::comment}
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
{:/}

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：

    trans x≡y (trans y≡z refl)

{::comment}
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
{:/}

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。


{::comment}
## Chains of equations, another example
{:/}

## 等式串的另外一个例子

{::comment}
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{:/}

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：

<pre class="Agda">{% raw %}<a id="11188" class="Keyword">data</a> <a id="ℕ"></a><a id="11193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="11195" class="Symbol">:</a> <a id="11197" class="PrimitiveType">Set</a> <a id="11201" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="11209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a> <a id="11214" class="Symbol">:</a> <a id="11216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="11220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a>  <a id="11225" class="Symbol">:</a> <a id="11227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="11229" class="Symbol">→</a> <a id="11231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="11234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">_+_</a> <a id="11238" class="Symbol">:</a> <a id="11240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="11242" class="Symbol">→</a> <a id="11244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="11246" class="Symbol">→</a> <a id="11248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a>
<a id="11250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a>    <a id="11258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11260" class="Bound">n</a>  <a id="11263" class="Symbol">=</a>  <a id="11266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11260" class="Bound">n</a>
<a id="11268" class="Symbol">(</a><a id="11269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="11273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11273" class="Bound">m</a><a id="11274" class="Symbol">)</a> <a id="11276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11278" class="Bound">n</a>  <a id="11281" class="Symbol">=</a>  <a id="11284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="11288" class="Symbol">(</a><a id="11289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11273" class="Bound">m</a> <a id="11291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11278" class="Bound">n</a><a id="11294" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
To save space we postulate (rather than prove in full) two lemmas:
{:/}

为了节约空间，我们假设两条引理（而不是证明它们）：

<pre class="Agda">{% raw %}<a id="11433" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="11445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11445" class="Postulate">+-identity</a> <a id="11456" class="Symbol">:</a> <a id="11458" class="Symbol">∀</a> <a id="11460" class="Symbol">(</a><a id="11461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11461" class="Bound">m</a> <a id="11463" class="Symbol">:</a> <a id="11465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="11466" class="Symbol">)</a> <a id="11468" class="Symbol">→</a> <a id="11470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11461" class="Bound">m</a> <a id="11472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a> <a id="11479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="11481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11461" class="Bound">m</a>
  <a id="+-suc"></a><a id="11485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11485" class="Postulate">+-suc</a> <a id="11491" class="Symbol">:</a> <a id="11493" class="Symbol">∀</a> <a id="11495" class="Symbol">(</a><a id="11496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11496" class="Bound">m</a> <a id="11498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11498" class="Bound">n</a> <a id="11500" class="Symbol">:</a> <a id="11502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="11503" class="Symbol">)</a> <a id="11505" class="Symbol">→</a> <a id="11507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11496" class="Bound">m</a> <a id="11509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="11515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11498" class="Bound">n</a> <a id="11517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="11519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="11523" class="Symbol">(</a><a id="11524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11496" class="Bound">m</a> <a id="11526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="11528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11498" class="Bound">n</a><a id="11529" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
{:/}

这是我们第一次使用*假设*（Postulate）。假设为一个标识符指定一个签名，但是不提供定义。我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，那么我们可以证明出任何东西。

{::comment}
We then repeat the proof of commutativity:
{:/}

我们接下来重复交换律的证明：

<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="12058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="12065" class="Symbol">:</a> <a id="12067" class="Symbol">∀</a> <a id="12069" class="Symbol">(</a><a id="12070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12070" class="Bound">m</a> <a id="12072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12072" class="Bound">n</a> <a id="12074" class="Symbol">:</a> <a id="12076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="12077" class="Symbol">)</a> <a id="12079" class="Symbol">→</a> <a id="12081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12070" class="Bound">m</a> <a id="12083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12072" class="Bound">n</a> <a id="12087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="12089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12072" class="Bound">n</a> <a id="12091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12070" class="Bound">m</a>
<a id="12095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="12102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12102" class="Bound">m</a> <a id="12104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a> <a id="12109" class="Symbol">=</a>
  <a id="12113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin</a>
    <a id="12123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12102" class="Bound">m</a> <a id="12125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a>
  <a id="12134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="12137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11445" class="Postulate">+-identity</a> <a id="12148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12102" class="Bound">m</a> <a id="12150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a>
    <a id="12156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12102" class="Bound">m</a>
  <a id="12160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7472" class="Function Operator">≡⟨⟩</a>
    <a id="12168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a> <a id="12173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12102" class="Bound">m</a>
  <a id="12179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">∎</a>
<a id="12181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="12188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a> <a id="12190" class="Symbol">(</a><a id="12191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a><a id="12196" class="Symbol">)</a> <a id="12198" class="Symbol">=</a>
  <a id="12202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7392" class="Function Operator">begin</a>
    <a id="12212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a> <a id="12214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a>
  <a id="12224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="12227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11485" class="Postulate">+-suc</a> <a id="12233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a> <a id="12235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a> <a id="12237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a>
    <a id="12243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12247" class="Symbol">(</a><a id="12248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a> <a id="12250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a><a id="12253" class="Symbol">)</a>
  <a id="12257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">≡⟨</a> <a id="12260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5844" class="Function">cong</a> <a id="12265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12269" class="Symbol">(</a><a id="12270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="12277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a> <a id="12279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a><a id="12280" class="Symbol">)</a> <a id="12282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7557" class="Function Operator">⟩</a>
    <a id="12288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12292" class="Symbol">(</a><a id="12293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a> <a id="12295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a><a id="12298" class="Symbol">)</a>
  <a id="12302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7472" class="Function Operator">≡⟨⟩</a>
    <a id="12310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="12314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12195" class="Bound">n</a> <a id="12316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="12318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12188" class="Bound">m</a>
  <a id="12322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7672" class="Function Operator">∎</a>{% endraw %}</pre>

{::comment}
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
{:/}

论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。

{::comment}
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
{:/}

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出

      suc (n + m)
    ≡⟨⟩
      suc n + m

{::comment}
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
{:/}

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出

      suc n + m
    ≡⟨⟩
      suc (n + m)

{::comment}
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
{:/}

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。而书写的顺序合不合理则是由我们自行决定。


{::comment}
#### Exercise `≤-Reasoning` (stretch)
{:/}

#### 练习 `≤-Reasoning` (延伸)

{::comment}
The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.
{:/}

[Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%}) 章节中的单调性证明亦可以用相似于 `≡-Reasoning` 的，更易于理解的形式给出。相似地来定义 `≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤`、`+-monoʳ-≤`
和 `+-mono-≤`。

{::comment}
<pre class="Agda">{% raw %}<a id="13913" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="13966" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Rewriting
{:/}

## 重写

{::comment}
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{:/}

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：

<pre class="Agda">{% raw %}<a id="14190" class="Keyword">data</a> <a id="even"></a><a id="14195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="14200" class="Symbol">:</a> <a id="14202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="14204" class="Symbol">→</a> <a id="14206" class="PrimitiveType">Set</a>
<a id="14210" class="Keyword">data</a> <a id="odd"></a><a id="14215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14215" class="Datatype">odd</a>  <a id="14220" class="Symbol">:</a> <a id="14222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a> <a id="14224" class="Symbol">→</a> <a id="14226" class="PrimitiveType">Set</a>

<a id="14231" class="Keyword">data</a> <a id="14236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="14241" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="14250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14250" class="InductiveConstructor">even-zero</a> <a id="14260" class="Symbol">:</a> <a id="14262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="14267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="14275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14275" class="InductiveConstructor">even-suc</a> <a id="14284" class="Symbol">:</a> <a id="14286" class="Symbol">∀</a> <a id="14288" class="Symbol">{</a><a id="14289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14289" class="Bound">n</a> <a id="14291" class="Symbol">:</a> <a id="14293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="14294" class="Symbol">}</a>
    <a id="14300" class="Symbol">→</a> <a id="14302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14215" class="Datatype">odd</a> <a id="14306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14289" class="Bound">n</a>
      <a id="14314" class="Comment">------------</a>
    <a id="14331" class="Symbol">→</a> <a id="14333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="14338" class="Symbol">(</a><a id="14339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="14343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14289" class="Bound">n</a><a id="14344" class="Symbol">)</a>

<a id="14347" class="Keyword">data</a> <a id="14352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14215" class="Datatype">odd</a> <a id="14356" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14364" class="InductiveConstructor">odd-suc</a> <a id="14372" class="Symbol">:</a> <a id="14374" class="Symbol">∀</a> <a id="14376" class="Symbol">{</a><a id="14377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14377" class="Bound">n</a> <a id="14379" class="Symbol">:</a> <a id="14381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="14382" class="Symbol">}</a>
    <a id="14388" class="Symbol">→</a> <a id="14390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="14395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14377" class="Bound">n</a>
      <a id="14403" class="Comment">-----------</a>
    <a id="14419" class="Symbol">→</a> <a id="14421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14215" class="Datatype">odd</a> <a id="14425" class="Symbol">(</a><a id="14426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="14430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14377" class="Bound">n</a><a id="14431" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
{:/}

在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。

{::comment}
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{:/}

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，我们只用编译程序指令来告诉 Agda 什么类型对应相等性：

<pre class="Agda">{% raw %}<a id="15042" class="Symbol">{-#</a> <a id="15046" class="Keyword">BUILTIN</a> EQUALITY <a id="15063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">_≡_</a> <a id="15067" class="Symbol">#-}</a>{% endraw %}</pre>

{::comment}
We can then prove the desired property as follows:
{:/}

我们然后就可以如下证明求证的性质：

<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="15184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15184" class="Function">even-comm</a> <a id="15194" class="Symbol">:</a> <a id="15196" class="Symbol">∀</a> <a id="15198" class="Symbol">(</a><a id="15199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15199" class="Bound">m</a> <a id="15201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15201" class="Bound">n</a> <a id="15203" class="Symbol">:</a> <a id="15205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="15206" class="Symbol">)</a>
  <a id="15210" class="Symbol">→</a> <a id="15212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="15217" class="Symbol">(</a><a id="15218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15199" class="Bound">m</a> <a id="15220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="15222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15201" class="Bound">n</a><a id="15223" class="Symbol">)</a>
    <a id="15229" class="Comment">------------</a>
  <a id="15244" class="Symbol">→</a> <a id="15246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="15251" class="Symbol">(</a><a id="15252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15201" class="Bound">n</a> <a id="15254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="15256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15199" class="Bound">m</a><a id="15257" class="Symbol">)</a>
<a id="15259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15184" class="Function">even-comm</a> <a id="15269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15269" class="Bound">m</a> <a id="15271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15271" class="Bound">n</a> <a id="15273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15273" class="Bound">ev</a>  <a id="15277" class="Keyword">rewrite</a> <a id="15285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="15292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15271" class="Bound">n</a> <a id="15294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15269" class="Bound">m</a>  <a id="15297" class="Symbol">=</a>  <a id="15300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15273" class="Bound">ev</a>{% endraw %}</pre>

{::comment}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
{:/}

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

{::comment}
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
{:/}

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
Now we add the rewrite:
{:/}

现在我们加入重写：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
{:/}

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。


{::comment}
## Multiple rewrites
{:/}

## 多重重写

{::comment}
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{:/}

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：

<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="17537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17537" class="Function">+-comm′</a> <a id="17545" class="Symbol">:</a> <a id="17547" class="Symbol">∀</a> <a id="17549" class="Symbol">(</a><a id="17550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17550" class="Bound">m</a> <a id="17552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17552" class="Bound">n</a> <a id="17554" class="Symbol">:</a> <a id="17556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="17557" class="Symbol">)</a> <a id="17559" class="Symbol">→</a> <a id="17561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17550" class="Bound">m</a> <a id="17563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="17565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17552" class="Bound">n</a> <a id="17567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="17569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17552" class="Bound">n</a> <a id="17571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="17573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17550" class="Bound">m</a>
<a id="17575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17537" class="Function">+-comm′</a> <a id="17583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="InductiveConstructor">zero</a>    <a id="17591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17591" class="Bound">n</a>  <a id="17594" class="Keyword">rewrite</a> <a id="17602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11445" class="Postulate">+-identity</a> <a id="17613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17591" class="Bound">n</a>             <a id="17627" class="Symbol">=</a>  <a id="17630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>
<a id="17635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17537" class="Function">+-comm′</a> <a id="17643" class="Symbol">(</a><a id="17644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11220" class="InductiveConstructor">suc</a> <a id="17648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17648" class="Bound">m</a><a id="17649" class="Symbol">)</a> <a id="17651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17651" class="Bound">n</a>  <a id="17654" class="Keyword">rewrite</a> <a id="17662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11485" class="Postulate">+-suc</a> <a id="17668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17651" class="Bound">n</a> <a id="17670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17648" class="Bound">m</a> <a id="17672" class="Symbol">|</a> <a id="17674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17537" class="Function">+-comm′</a> <a id="17682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17648" class="Bound">m</a> <a id="17684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17651" class="Bound">n</a>  <a id="17687" class="Symbol">=</a>  <a id="17690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
{:/}

这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将合同性考虑在其中。尽管使用重写的证明更加的简短，使用等式串的证明能容易理解，我们将尽可能的使用后者。


{::comment}
## Rewriting expanded
{:/}

## 深入重写

{::comment}
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{:/}

`rewrite` 记法实际上是 `with` 抽象的一种应用：

<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="18494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18494" class="Function">even-comm′</a> <a id="18505" class="Symbol">:</a> <a id="18507" class="Symbol">∀</a> <a id="18509" class="Symbol">(</a><a id="18510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18510" class="Bound">m</a> <a id="18512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18512" class="Bound">n</a> <a id="18514" class="Symbol">:</a> <a id="18516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="18517" class="Symbol">)</a>
  <a id="18521" class="Symbol">→</a> <a id="18523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="18528" class="Symbol">(</a><a id="18529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18510" class="Bound">m</a> <a id="18531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="18533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18512" class="Bound">n</a><a id="18534" class="Symbol">)</a>
    <a id="18540" class="Comment">------------</a>
  <a id="18555" class="Symbol">→</a> <a id="18557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="18562" class="Symbol">(</a><a id="18563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18512" class="Bound">n</a> <a id="18565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="18567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18510" class="Bound">m</a><a id="18568" class="Symbol">)</a>
<a id="18570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18494" class="Function">even-comm′</a> <a id="18581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18581" class="Bound">m</a> <a id="18583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18583" class="Bound">n</a> <a id="18585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18585" class="Bound">ev</a> <a id="18588" class="Keyword">with</a>   <a id="18595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18581" class="Bound">m</a> <a id="18597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="18599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18583" class="Bound">n</a>  <a id="18602" class="Symbol">|</a> <a id="18604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="18611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18581" class="Bound">m</a> <a id="18613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18583" class="Bound">n</a>
<a id="18615" class="Symbol">...</a>                  <a id="18636" class="Symbol">|</a> <a id="18638" class="DottedPattern Symbol">.(</a><a id="18640" class="DottedPattern Bound">n</a> <a id="18642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="DottedPattern Function Operator">+</a> <a id="18644" class="DottedPattern Bound">m</a><a id="18645" class="DottedPattern Symbol">)</a> <a id="18647" class="Symbol">|</a> <a id="18649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>       <a id="18660" class="Symbol">=</a> <a id="18662" class="Bound">ev</a>{% endraw %}</pre>

{::comment}
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
{:/}

总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。注意在这里使用的*点模式*（Dot Pattern），`.(n + m)`。点模式由一个点和一个表达式组成，在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴含了需要的信息。但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）

{::comment}
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{:/}

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：

<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="20247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20247" class="Function">even-comm″</a> <a id="20258" class="Symbol">:</a> <a id="20260" class="Symbol">∀</a> <a id="20262" class="Symbol">(</a><a id="20263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20263" class="Bound">m</a> <a id="20265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20265" class="Bound">n</a> <a id="20267" class="Symbol">:</a> <a id="20269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11193" class="Datatype">ℕ</a><a id="20270" class="Symbol">)</a>
  <a id="20274" class="Symbol">→</a> <a id="20276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="20281" class="Symbol">(</a><a id="20282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20263" class="Bound">m</a> <a id="20284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="20286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20265" class="Bound">n</a><a id="20287" class="Symbol">)</a>
    <a id="20293" class="Comment">------------</a>
  <a id="20308" class="Symbol">→</a> <a id="20310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="20315" class="Symbol">(</a><a id="20316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20265" class="Bound">n</a> <a id="20318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11234" class="Function Operator">+</a> <a id="20320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20263" class="Bound">m</a><a id="20321" class="Symbol">)</a>
<a id="20323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20247" class="Function">even-comm″</a> <a id="20334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20334" class="Bound">m</a> <a id="20336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20336" class="Bound">n</a>  <a id="20339" class="Symbol">=</a>  <a id="20342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6810" class="Function">subst</a> <a id="20348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14195" class="Datatype">even</a> <a id="20353" class="Symbol">(</a><a id="20354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12058" class="Function">+-comm</a> <a id="20361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20334" class="Bound">m</a> <a id="20363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20336" class="Bound">n</a><a id="20364" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
{:/}

尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。


{::comment}
## Leibniz equality
{:/}

## 莱布尼兹（Leibniz）相等性

{::comment}
The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.
{:/}

我们使用的相等性断言的形式源于 Martin Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，于 1686 年发表。莱布尼兹断言的相等性表示*不可分辨的实体*（Identity of Indiscernibles）：两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），与史波克定律紧密相关：“一个不造成区别的区别不是区别”。我们在这里定义莱布尼兹相等性，并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin Löf 相等性。

{::comment}
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
{:/}

莱布尼兹不等式一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。

{::comment}
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{:/}

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，我们有 `P x` 蕴含了 `P y`：

<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="22123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">_≐_</a> <a id="22127" class="Symbol">:</a> <a id="22129" class="Symbol">∀</a> <a id="22131" class="Symbol">{</a><a id="22132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22132" class="Bound">A</a> <a id="22134" class="Symbol">:</a> <a id="22136" class="PrimitiveType">Set</a><a id="22139" class="Symbol">}</a> <a id="22141" class="Symbol">(</a><a id="22142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22142" class="Bound">x</a> <a id="22144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22144" class="Bound">y</a> <a id="22146" class="Symbol">:</a> <a id="22148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22132" class="Bound">A</a><a id="22149" class="Symbol">)</a> <a id="22151" class="Symbol">→</a> <a id="22153" class="PrimitiveType">Set₁</a>
<a id="22158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">_≐_</a> <a id="22162" class="Symbol">{</a><a id="22163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22163" class="Bound">A</a><a id="22164" class="Symbol">}</a> <a id="22166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22166" class="Bound">x</a> <a id="22168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22168" class="Bound">y</a> <a id="22170" class="Symbol">=</a> <a id="22172" class="Symbol">∀</a> <a id="22174" class="Symbol">(</a><a id="22175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22175" class="Bound">P</a> <a id="22177" class="Symbol">:</a> <a id="22179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22163" class="Bound">A</a> <a id="22181" class="Symbol">→</a> <a id="22183" class="PrimitiveType">Set</a><a id="22186" class="Symbol">)</a> <a id="22188" class="Symbol">→</a> <a id="22190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22175" class="Bound">P</a> <a id="22192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22166" class="Bound">x</a> <a id="22194" class="Symbol">→</a> <a id="22196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22175" class="Bound">P</a> <a id="22198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22168" class="Bound">y</a>{% endraw %}</pre>

{::comment}
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
{:/}

我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。

{::comment}
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
{:/}

这是我们第一次使用*等级*（Levels）。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。

{::comment}
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{:/}

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：

<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="23438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23438" class="Function">refl-≐</a> <a id="23445" class="Symbol">:</a> <a id="23447" class="Symbol">∀</a> <a id="23449" class="Symbol">{</a><a id="23450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23450" class="Bound">A</a> <a id="23452" class="Symbol">:</a> <a id="23454" class="PrimitiveType">Set</a><a id="23457" class="Symbol">}</a> <a id="23459" class="Symbol">{</a><a id="23460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23460" class="Bound">x</a> <a id="23462" class="Symbol">:</a> <a id="23464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23450" class="Bound">A</a><a id="23465" class="Symbol">}</a>
  <a id="23469" class="Symbol">→</a> <a id="23471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23460" class="Bound">x</a> <a id="23473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23460" class="Bound">x</a>
<a id="23477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23438" class="Function">refl-≐</a> <a id="23484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23484" class="Bound">P</a> <a id="23486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23486" class="Bound">Px</a>  <a id="23490" class="Symbol">=</a>  <a id="23493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23486" class="Bound">Px</a>

<a id="trans-≐"></a><a id="23497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23497" class="Function">trans-≐</a> <a id="23505" class="Symbol">:</a> <a id="23507" class="Symbol">∀</a> <a id="23509" class="Symbol">{</a><a id="23510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23510" class="Bound">A</a> <a id="23512" class="Symbol">:</a> <a id="23514" class="PrimitiveType">Set</a><a id="23517" class="Symbol">}</a> <a id="23519" class="Symbol">{</a><a id="23520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23520" class="Bound">x</a> <a id="23522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23522" class="Bound">y</a> <a id="23524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23524" class="Bound">z</a> <a id="23526" class="Symbol">:</a> <a id="23528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23510" class="Bound">A</a><a id="23529" class="Symbol">}</a>
  <a id="23533" class="Symbol">→</a> <a id="23535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23520" class="Bound">x</a> <a id="23537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23522" class="Bound">y</a>
  <a id="23543" class="Symbol">→</a> <a id="23545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23522" class="Bound">y</a> <a id="23547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23524" class="Bound">z</a>
    <a id="23555" class="Comment">-----</a>
  <a id="23563" class="Symbol">→</a> <a id="23565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23520" class="Bound">x</a> <a id="23567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23524" class="Bound">z</a>
<a id="23571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23497" class="Function">trans-≐</a> <a id="23579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23579" class="Bound">x≐y</a> <a id="23583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23583" class="Bound">y≐z</a> <a id="23587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23587" class="Bound">P</a> <a id="23589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23589" class="Bound">Px</a>  <a id="23593" class="Symbol">=</a>  <a id="23596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23583" class="Bound">y≐z</a> <a id="23600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23587" class="Bound">P</a> <a id="23602" class="Symbol">(</a><a id="23603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23579" class="Bound">x≐y</a> <a id="23607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23587" class="Bound">P</a> <a id="23609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23589" class="Bound">Px</a><a id="23611" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{:/}

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴含 `P y`，那么反方向的蕴含也成立。

<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="23868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23868" class="Function">sym-≐</a> <a id="23874" class="Symbol">:</a> <a id="23876" class="Symbol">∀</a> <a id="23878" class="Symbol">{</a><a id="23879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23879" class="Bound">A</a> <a id="23881" class="Symbol">:</a> <a id="23883" class="PrimitiveType">Set</a><a id="23886" class="Symbol">}</a> <a id="23888" class="Symbol">{</a><a id="23889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23889" class="Bound">x</a> <a id="23891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23891" class="Bound">y</a> <a id="23893" class="Symbol">:</a> <a id="23895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23879" class="Bound">A</a><a id="23896" class="Symbol">}</a>
  <a id="23900" class="Symbol">→</a> <a id="23902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23889" class="Bound">x</a> <a id="23904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23891" class="Bound">y</a>
    <a id="23912" class="Comment">-----</a>
  <a id="23920" class="Symbol">→</a> <a id="23922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23891" class="Bound">y</a> <a id="23924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="23926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23889" class="Bound">x</a>
<a id="23928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23868" class="Function">sym-≐</a> <a id="23934" class="Symbol">{</a><a id="23935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23935" class="Bound">A</a><a id="23936" class="Symbol">}</a> <a id="23938" class="Symbol">{</a><a id="23939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23939" class="Bound">x</a><a id="23940" class="Symbol">}</a> <a id="23942" class="Symbol">{</a><a id="23943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23943" class="Bound">y</a><a id="23944" class="Symbol">}</a> <a id="23946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23946" class="Bound">x≐y</a> <a id="23950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23950" class="Bound">P</a>  <a id="23953" class="Symbol">=</a>  <a id="23956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24038" class="Function">Qy</a>
  <a id="23961" class="Keyword">where</a>
    <a id="23971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23971" class="Function">Q</a> <a id="23973" class="Symbol">:</a> <a id="23975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23935" class="Bound">A</a> <a id="23977" class="Symbol">→</a> <a id="23979" class="PrimitiveType">Set</a>
    <a id="23987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23971" class="Function">Q</a> <a id="23989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23989" class="Bound">z</a> <a id="23991" class="Symbol">=</a> <a id="23993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23950" class="Bound">P</a> <a id="23995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23989" class="Bound">z</a> <a id="23997" class="Symbol">→</a> <a id="23999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23950" class="Bound">P</a> <a id="24001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23939" class="Bound">x</a>
    <a id="24007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24007" class="Function">Qx</a> <a id="24010" class="Symbol">:</a> <a id="24012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23971" class="Function">Q</a> <a id="24014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23939" class="Bound">x</a>
    <a id="24020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24007" class="Function">Qx</a> <a id="24023" class="Symbol">=</a> <a id="24025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23438" class="Function">refl-≐</a> <a id="24032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23950" class="Bound">P</a>
    <a id="24038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24038" class="Function">Qy</a> <a id="24041" class="Symbol">:</a> <a id="24043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23971" class="Function">Q</a> <a id="24045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23943" class="Bound">y</a>
    <a id="24051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24038" class="Function">Qy</a> <a id="24054" class="Symbol">=</a> <a id="24056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23946" class="Bound">x≐y</a> <a id="24060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23971" class="Function">Q</a> <a id="24062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24007" class="Function">Qx</a>{% endraw %}</pre>

{::comment}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.
{:/}

给定 `x ≐ y` 和一个特定的 `P`，我们需要构造一个 `P y` 蕴含 `P x` 的证明。我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴含 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，由此通过 `x ≐ y` 就能推出 `Q y` 成立。而 `Q y`
正是我们需要的证明，即 `P y` 蕴含 `P x`。

{::comment}
We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{:/}

我们现在来证明 Martin Löf 相等性蕴含了莱布尼兹相等性，以及其逆命题。在正方向上，如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。

<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="25127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25127" class="Function">≡-implies-≐</a> <a id="25139" class="Symbol">:</a> <a id="25141" class="Symbol">∀</a> <a id="25143" class="Symbol">{</a><a id="25144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25144" class="Bound">A</a> <a id="25146" class="Symbol">:</a> <a id="25148" class="PrimitiveType">Set</a><a id="25151" class="Symbol">}</a> <a id="25153" class="Symbol">{</a><a id="25154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25154" class="Bound">x</a> <a id="25156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25156" class="Bound">y</a> <a id="25158" class="Symbol">:</a> <a id="25160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25144" class="Bound">A</a><a id="25161" class="Symbol">}</a>
  <a id="25165" class="Symbol">→</a> <a id="25167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25154" class="Bound">x</a> <a id="25169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="25171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25156" class="Bound">y</a>
    <a id="25177" class="Comment">-----</a>
  <a id="25185" class="Symbol">→</a> <a id="25187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25154" class="Bound">x</a> <a id="25189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="25191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25156" class="Bound">y</a>
<a id="25193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25127" class="Function">≡-implies-≐</a> <a id="25205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25205" class="Bound">x≡y</a> <a id="25209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25209" class="Bound">P</a>  <a id="25212" class="Symbol">=</a>  <a id="25215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6810" class="Function">subst</a> <a id="25221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25209" class="Bound">P</a> <a id="25223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25205" class="Bound">x≡y</a>{% endraw %}</pre>

{::comment}
This direction follows from substitution, which we showed earlier.
{:/}

因为这个方向由替换性可以得来，如之前证明的那样。

{::comment}
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{:/}

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，我们需要证明 `x ≡ y`：

<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="25570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25570" class="Function">≐-implies-≡</a> <a id="25582" class="Symbol">:</a> <a id="25584" class="Symbol">∀</a> <a id="25586" class="Symbol">{</a><a id="25587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25587" class="Bound">A</a> <a id="25589" class="Symbol">:</a> <a id="25591" class="PrimitiveType">Set</a><a id="25594" class="Symbol">}</a> <a id="25596" class="Symbol">{</a><a id="25597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25597" class="Bound">x</a> <a id="25599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25599" class="Bound">y</a> <a id="25601" class="Symbol">:</a> <a id="25603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25587" class="Bound">A</a><a id="25604" class="Symbol">}</a>
  <a id="25608" class="Symbol">→</a> <a id="25610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25597" class="Bound">x</a> <a id="25612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#22123" class="Function Operator">≐</a> <a id="25614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25599" class="Bound">y</a>
    <a id="25620" class="Comment">-----</a>
  <a id="25628" class="Symbol">→</a> <a id="25630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25597" class="Bound">x</a> <a id="25632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="25634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25599" class="Bound">y</a>
<a id="25636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25570" class="Function">≐-implies-≡</a> <a id="25648" class="Symbol">{</a><a id="25649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25649" class="Bound">A</a><a id="25650" class="Symbol">}</a> <a id="25652" class="Symbol">{</a><a id="25653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25653" class="Bound">x</a><a id="25654" class="Symbol">}</a> <a id="25656" class="Symbol">{</a><a id="25657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25657" class="Bound">y</a><a id="25658" class="Symbol">}</a> <a id="25660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25660" class="Bound">x≐y</a>  <a id="25665" class="Symbol">=</a>  <a id="25668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25742" class="Function">Qy</a>
  <a id="25673" class="Keyword">where</a>
    <a id="25683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25683" class="Function">Q</a> <a id="25685" class="Symbol">:</a> <a id="25687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25649" class="Bound">A</a> <a id="25689" class="Symbol">→</a> <a id="25691" class="PrimitiveType">Set</a>
    <a id="25699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25683" class="Function">Q</a> <a id="25701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25701" class="Bound">z</a> <a id="25703" class="Symbol">=</a> <a id="25705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25653" class="Bound">x</a> <a id="25707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1078" class="Datatype Operator">≡</a> <a id="25709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25701" class="Bound">z</a>
    <a id="25715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25715" class="Function">Qx</a> <a id="25718" class="Symbol">:</a> <a id="25720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25683" class="Function">Q</a> <a id="25722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25653" class="Bound">x</a>
    <a id="25728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25715" class="Function">Qx</a> <a id="25731" class="Symbol">=</a> <a id="25733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1118" class="InductiveConstructor">refl</a>
    <a id="25742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25742" class="Function">Qy</a> <a id="25745" class="Symbol">:</a> <a id="25747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25683" class="Function">Q</a> <a id="25749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25657" class="Bound">y</a>
    <a id="25755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25742" class="Function">Qy</a> <a id="25758" class="Symbol">=</a> <a id="25760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25660" class="Bound">x≐y</a> <a id="25764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25683" class="Function">Q</a> <a id="25766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25715" class="Function">Qx</a>{% endraw %}</pre>

{::comment}
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
{:/}

此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。

{::comment}
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
{:/}

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，草稿，2017）


{::comment}
## Universe polymorphism {#unipoly}
{:/}

## 全体多态 {#unipoly}

{::comment}
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
{:/}

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？

{::comment}
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{:/}

答案是*全体多态*（Universe Polymorphism），一个定义可以根据任何等级 `ℓ` 来做出。为了使用等级，我们首先导入下列内容：

<pre class="Agda">{% raw %}<a id="27661" class="Keyword">open</a> <a id="27666" class="Keyword">import</a> <a id="27673" href="https://agda.github.io/agda-stdlib/v0.17/Level.html" class="Module">Level</a> <a id="27679" class="Keyword">using</a> <a id="27685" class="Symbol">(</a><a id="27686" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#408" class="Postulate">Level</a><a id="27691" class="Symbol">;</a> <a id="27693" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="27696" class="Symbol">)</a> <a id="27698" class="Keyword">renaming</a> <a id="27707" class="Symbol">(</a><a id="27708" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="27713" class="Symbol">to</a> <a id="27716" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="27721" class="Symbol">;</a> <a id="27723" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="27727" class="Symbol">to</a> <a id="27730" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="27734" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
{:/}

我们将构造器 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。

{::comment}
Levels are isomorphic to natural numbers, and have similar constructors:
{:/}

等级与自然数是同构的，有相似的构造器：

    lzero : Level
    lsuc  : Level → Level

{::comment}
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
{:/}

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

{::comment}
and so on. There is also an operator
{:/}

以此类推。我们还有一个运算符：

    _⊔_ : Level → Level → Level

{::comment}
that given two levels returns the larger of the two.
{:/}

给定两个等级，返回两者中较大的那个。

{::comment}
Here is the definition of equality, generalised to an arbitrary level:
{:/}

下面是相等性的定义，推广到任意等级：

<pre class="Agda">{% raw %}<a id="28596" class="Keyword">data</a> <a id="_≡′_"></a><a id="28601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28601" class="Datatype Operator">_≡′_</a> <a id="28606" class="Symbol">{</a><a id="28607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28607" class="Bound">ℓ</a> <a id="28609" class="Symbol">:</a> <a id="28611" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28616" class="Symbol">}</a> <a id="28618" class="Symbol">{</a><a id="28619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28619" class="Bound">A</a> <a id="28621" class="Symbol">:</a> <a id="28623" class="PrimitiveType">Set</a> <a id="28627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28607" class="Bound">ℓ</a><a id="28628" class="Symbol">}</a> <a id="28630" class="Symbol">(</a><a id="28631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28631" class="Bound">x</a> <a id="28633" class="Symbol">:</a> <a id="28635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28619" class="Bound">A</a><a id="28636" class="Symbol">)</a> <a id="28638" class="Symbol">:</a> <a id="28640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28619" class="Bound">A</a> <a id="28642" class="Symbol">→</a> <a id="28644" class="PrimitiveType">Set</a> <a id="28648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28607" class="Bound">ℓ</a> <a id="28650" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="28658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28658" class="InductiveConstructor">refl′</a> <a id="28664" class="Symbol">:</a> <a id="28666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28631" class="Bound">x</a> <a id="28668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28601" class="Datatype Operator">≡′</a> <a id="28671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28631" class="Bound">x</a>{% endraw %}</pre>

{::comment}
Similarly, here is the generalised definition of symmetry:
{:/}

相似的，下面是对称性的推广定义：

<pre class="Agda">{% raw %}<a id="sym′"></a><a id="28793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28793" class="Function">sym′</a> <a id="28798" class="Symbol">:</a> <a id="28800" class="Symbol">∀</a> <a id="28802" class="Symbol">{</a><a id="28803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28803" class="Bound">ℓ</a> <a id="28805" class="Symbol">:</a> <a id="28807" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28812" class="Symbol">}</a> <a id="28814" class="Symbol">{</a><a id="28815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28815" class="Bound">A</a> <a id="28817" class="Symbol">:</a> <a id="28819" class="PrimitiveType">Set</a> <a id="28823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28803" class="Bound">ℓ</a><a id="28824" class="Symbol">}</a> <a id="28826" class="Symbol">{</a><a id="28827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28827" class="Bound">x</a> <a id="28829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28829" class="Bound">y</a> <a id="28831" class="Symbol">:</a> <a id="28833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28815" class="Bound">A</a><a id="28834" class="Symbol">}</a>
  <a id="28838" class="Symbol">→</a> <a id="28840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28827" class="Bound">x</a> <a id="28842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28601" class="Datatype Operator">≡′</a> <a id="28845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28829" class="Bound">y</a>
    <a id="28851" class="Comment">------</a>
  <a id="28860" class="Symbol">→</a> <a id="28862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28829" class="Bound">y</a> <a id="28864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28601" class="Datatype Operator">≡′</a> <a id="28867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28827" class="Bound">x</a>
<a id="28869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28793" class="Function">sym′</a> <a id="28874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28658" class="InductiveConstructor">refl′</a> <a id="28880" class="Symbol">=</a> <a id="28882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28658" class="InductiveConstructor">refl′</a>{% endraw %}</pre>

{::comment}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
{:/}

为了简介，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，包括相等性的定义，都推广到了任意等级，如上所示。

{::comment}
Here is the generalised definition of Leibniz equality:
{:/}

下面是莱布尼兹相等性的推广定义：

<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="29296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29296" class="Function Operator">_≐′_</a> <a id="29301" class="Symbol">:</a> <a id="29303" class="Symbol">∀</a> <a id="29305" class="Symbol">{</a><a id="29306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29306" class="Bound">ℓ</a> <a id="29308" class="Symbol">:</a> <a id="29310" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#408" class="Postulate">Level</a><a id="29315" class="Symbol">}</a> <a id="29317" class="Symbol">{</a><a id="29318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29318" class="Bound">A</a> <a id="29320" class="Symbol">:</a> <a id="29322" class="PrimitiveType">Set</a> <a id="29326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29306" class="Bound">ℓ</a><a id="29327" class="Symbol">}</a> <a id="29329" class="Symbol">(</a><a id="29330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29330" class="Bound">x</a> <a id="29332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29332" class="Bound">y</a> <a id="29334" class="Symbol">:</a> <a id="29336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29318" class="Bound">A</a><a id="29337" class="Symbol">)</a> <a id="29339" class="Symbol">→</a> <a id="29341" class="PrimitiveType">Set</a> <a id="29345" class="Symbol">(</a><a id="29346" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="29351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29306" class="Bound">ℓ</a><a id="29352" class="Symbol">)</a>
<a id="29354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29296" class="Function Operator">_≐′_</a> <a id="29359" class="Symbol">{</a><a id="29360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29360" class="Bound">ℓ</a><a id="29361" class="Symbol">}</a> <a id="29363" class="Symbol">{</a><a id="29364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29364" class="Bound">A</a><a id="29365" class="Symbol">}</a> <a id="29367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29367" class="Bound">x</a> <a id="29369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29369" class="Bound">y</a> <a id="29371" class="Symbol">=</a> <a id="29373" class="Symbol">∀</a> <a id="29375" class="Symbol">(</a><a id="29376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29376" class="Bound">P</a> <a id="29378" class="Symbol">:</a> <a id="29380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29364" class="Bound">A</a> <a id="29382" class="Symbol">→</a> <a id="29384" class="PrimitiveType">Set</a> <a id="29388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29360" class="Bound">ℓ</a><a id="29389" class="Symbol">)</a> <a id="29391" class="Symbol">→</a> <a id="29393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29376" class="Bound">P</a> <a id="29395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29367" class="Bound">x</a> <a id="29397" class="Symbol">→</a> <a id="29399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29376" class="Bound">P</a> <a id="29401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#29369" class="Bound">y</a>{% endraw %}</pre>

{::comment}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
{:/}

之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。

{::comment}
Further information on levels can be found in the [Agda Wiki][wiki].
{:/}

更多的关于等级的信息可以从[Agda 维基（英文）][wiki]中查询。

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the
standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

<pre class="Agda">{% raw %}<a id="30088" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="30142" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="30206" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>

{::comment}
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
{:/}

这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
{:/}

本章节使用下列 Unicode：

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  接近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
