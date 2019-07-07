---
src       : src/plfa/Relations.lagda
title     : "Relations: 关系的归纳定义"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
translators : ["Fangyi Zhou"]
progress  : 100
---

<pre class="Agda">{% raw %}<a id="190" class="Keyword">module</a> <a id="197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="212" class="Keyword">where</a>{% endraw %}</pre>
{::comment}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.
{:/}

在定义了加法和乘法等运算以后，下一步我们来定义**关系（Relation）**，比如说**小于等于**。


{::comment}
## Imports
{:/}

## 导入

<pre class="Agda">{% raw %}<a id="488" class="Keyword">import</a> <a id="495" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="533" class="Symbol">as</a> <a id="536" class="Module">Eq</a>
<a id="539" class="Keyword">open</a> <a id="544" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="547" class="Keyword">using</a> <a id="553" class="Symbol">(</a><a id="554" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="557" class="Symbol">;</a> <a id="559" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="563" class="Symbol">;</a> <a id="565" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="569" class="Symbol">)</a>
<a id="571" class="Keyword">open</a> <a id="576" class="Keyword">import</a> <a id="583" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="592" class="Keyword">using</a> <a id="598" class="Symbol">(</a><a id="599" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="600" class="Symbol">;</a> <a id="602" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="606" class="Symbol">;</a> <a id="608" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="611" class="Symbol">;</a> <a id="613" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="616" class="Symbol">)</a>
<a id="618" class="Keyword">open</a> <a id="623" class="Keyword">import</a> <a id="630" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="650" class="Keyword">using</a> <a id="656" class="Symbol">(</a><a id="657" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="663" class="Symbol">)</a>{% endraw %}</pre>


{::comment}
## Defining relations
{:/}

## 定义关系

{::comment}
The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:
{:/}

小于等于这个关系有无穷个实例，如下所示：


    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

{::comment}
And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:
{:/}

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

{::comment}
And here is the definition in Agda:
{:/}

以及其 Agda 定义：

<pre class="Agda">{% raw %}<a id="1496" class="Keyword">data</a> <a id="_≤_"></a><a id="1501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">_≤_</a> <a id="1505" class="Symbol">:</a> <a id="1507" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1509" class="Symbol">→</a> <a id="1511" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1513" class="Symbol">→</a> <a id="1515" class="PrimitiveType">Set</a> <a id="1519" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a> <a id="1532" class="Symbol">:</a> <a id="1534" class="Symbol">∀</a> <a id="1536" class="Symbol">{</a><a id="1537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="Bound">n</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1542" class="Symbol">}</a>
      <a id="1550" class="Comment">--------</a>
    <a id="1563" class="Symbol">→</a> <a id="1565" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="1572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="1581" class="Symbol">:</a> <a id="1583" class="Symbol">∀</a> <a id="1585" class="Symbol">{</a><a id="1586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1586" class="Bound">m</a> <a id="1588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1588" class="Bound">n</a> <a id="1590" class="Symbol">:</a> <a id="1592" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1593" class="Symbol">}</a>
    <a id="1599" class="Symbol">→</a> <a id="1601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1586" class="Bound">m</a> <a id="1603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="1605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1588" class="Bound">n</a>
      <a id="1613" class="Comment">-------------</a>
    <a id="1631" class="Symbol">→</a> <a id="1633" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1586" class="Bound">m</a> <a id="1639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="1641" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1588" class="Bound">n</a>{% endraw %}</pre>

{::comment}
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.
{:/}

在这里，`z≤n` 和 `s≤s`（无空格）是构造器的名称，`zero ≤ n`、`m ≤ n` 和
`suc m ≤ suc n` （带空格）是类型。在这里我们第一次用到了
**索引数据类型（Indexed datatype）**。我们使用 `m` 和 `n` 这两个自然数来索引
`m ≤ n` 这个类型。在 Agda 里，由两个及以上短横线开始的行是注释行，我们巧妙利用这一语法特性，用上述形式来表示相应的推理规则。在后文中，我们还会继续使用这一形式。

{::comment}
Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.
{:/}

这两条定义告诉我们相同的两件事：

* **起始步骤**: 对于所有的自然数 `n`，命题 `zero ≤ n` 成立。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，如果命题 `m ≤ n` 成立，
  那么命题 `suc m ≤ suc n` 成立。

{::comment}
In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.
{:/}

实际上，他们分别给我们更多的信息：

* **起始步骤**: 对于所有的自然数 `n`，构造器 `z≤n` 提供了 `zero ≤ n` 成立的证明。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，构造器 `s≤s` 将 `m ≤ n` 成立的证明
  转化为 `suc m ≤ suc n` 成立的证明。

{::comment}
For example, here in inference rule notation is the proof that
`2 ≤ 4`:
{:/}

例如，我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

{::comment}
And here is the corresponding Agda proof:
{:/}

下面是对应的 Agda 证明：

<pre class="Agda">{% raw %}<a id="3591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3591" class="Function">_</a> <a id="3593" class="Symbol">:</a> <a id="3595" class="Number">2</a> <a id="3597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="3599" class="Number">4</a>
<a id="3601" class="Symbol">_</a> <a id="3603" class="Symbol">=</a> <a id="3605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="3609" class="Symbol">(</a><a id="3610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="3614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a><a id="3617" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
## Implicit arguments
{:/}

## 隐式参数

{::comment}
This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:
{:/}

这是我们第一次使用隐式参数。定义不等式时，构造器的定义中使用了 `∀`，就像我们在下面的命题中使用 `∀` 一样：

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.
{:/}

但是我们这里的定义使用了花括号 `{ }`，而不是小括号 `( )`。这意味着参数是**隐式的（Implicit）**，不需要额外声明。实际上，Agda 的类型检查器会**推导（Infer）**出它们。因此，我们在 `m + n ≡ n + m` 的证明中需要写出 `+-comm m n`，在 `zero ≤ n` 的证明中可以省略 `n`。同理，如果 `m≤n` 是 `m ≤ n`的证明，那么我们写出 `s≤s m≤n` 作为 `suc m ≤ suc n` 的证明，无需声明 `m` 和 `n`。

{::comment}
If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{:/}

如果有希望的话，我们也可以在大括号里显式声明隐式参数。例如，下面是 `2 ≤ 4` 的 Agda
证明，包括了显式声明了的隐式参数：

<pre class="Agda">{% raw %}<a id="5073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5073" class="Function">_</a> <a id="5075" class="Symbol">:</a> <a id="5077" class="Number">2</a> <a id="5079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="5081" class="Number">4</a>
<a id="5083" class="Symbol">_</a> <a id="5085" class="Symbol">=</a> <a id="5087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5091" class="Symbol">{</a><a id="5092" class="Number">1</a><a id="5093" class="Symbol">}</a> <a id="5095" class="Symbol">{</a><a id="5096" class="Number">3</a><a id="5097" class="Symbol">}</a> <a id="5099" class="Symbol">(</a><a id="5100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5104" class="Symbol">{</a><a id="5105" class="Number">0</a><a id="5106" class="Symbol">}</a> <a id="5108" class="Symbol">{</a><a id="5109" class="Number">2</a><a id="5110" class="Symbol">}</a> <a id="5112" class="Symbol">(</a><a id="5113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a> <a id="5117" class="Symbol">{</a><a id="5118" class="Number">2</a><a id="5119" class="Symbol">}))</a>{% endraw %}</pre>

{::comment}
One may also identify implicit arguments by name:
{:/}

也可以额外加上参数的名字：

<pre class="Agda">{% raw %}<a id="5231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5231" class="Function">_</a> <a id="5233" class="Symbol">:</a> <a id="5235" class="Number">2</a> <a id="5237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="5239" class="Number">4</a>
<a id="5241" class="Symbol">_</a> <a id="5243" class="Symbol">=</a> <a id="5245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5249" class="Symbol">{</a><a id="5250" class="Argument">m</a> <a id="5252" class="Symbol">=</a> <a id="5254" class="Number">1</a><a id="5255" class="Symbol">}</a> <a id="5257" class="Symbol">{</a><a id="5258" class="Argument">n</a> <a id="5260" class="Symbol">=</a> <a id="5262" class="Number">3</a><a id="5263" class="Symbol">}</a> <a id="5265" class="Symbol">(</a><a id="5266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5270" class="Symbol">{</a><a id="5271" class="Argument">m</a> <a id="5273" class="Symbol">=</a> <a id="5275" class="Number">0</a><a id="5276" class="Symbol">}</a> <a id="5278" class="Symbol">{</a><a id="5279" class="Argument">n</a> <a id="5281" class="Symbol">=</a> <a id="5283" class="Number">2</a><a id="5284" class="Symbol">}</a> <a id="5286" class="Symbol">(</a><a id="5287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a> <a id="5291" class="Symbol">{</a><a id="5292" class="Argument">n</a> <a id="5294" class="Symbol">=</a> <a id="5296" class="Number">2</a><a id="5297" class="Symbol">}))</a>{% endraw %}</pre>

{::comment}
In the latter format, you may only supply some implicit arguments:
{:/}

在后者的形式中，也可以只声明一部分隐式参数：

<pre class="Agda">{% raw %}<a id="5435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5435" class="Function">_</a> <a id="5437" class="Symbol">:</a> <a id="5439" class="Number">2</a> <a id="5441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="5443" class="Number">4</a>
<a id="5445" class="Symbol">_</a> <a id="5447" class="Symbol">=</a> <a id="5449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5453" class="Symbol">{</a><a id="5454" class="Argument">n</a> <a id="5456" class="Symbol">=</a> <a id="5458" class="Number">3</a><a id="5459" class="Symbol">}</a> <a id="5461" class="Symbol">(</a><a id="5462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="5466" class="Symbol">{</a><a id="5467" class="Argument">n</a> <a id="5469" class="Symbol">=</a> <a id="5471" class="Number">2</a><a id="5472" class="Symbol">}</a> <a id="5474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a><a id="5477" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
It is not permitted to swap implicit arguments, even when named.
{:/}

但是不可以改变隐式参数的顺序，即便加上了名字。


{::comment}
## Precedence
{:/}

## 优先级

{::comment}
We declare the precedence for comparison as follows:
{:/}

我们如下定义比较的优先级：

<pre class="Agda">{% raw %}<a id="5739" class="Keyword">infix</a> <a id="5745" class="Number">4</a> <a id="5747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">_≤_</a>{% endraw %}</pre>

{::comment}
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.
{:/}

我们将 `_≤_` 的优先级设置为 4，所以它比优先级为 6 的 `_+_` 结合的更紧，此外，
`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`。我们用 `infix` 来表示运算符既不是左结合的，也不是右结合的。因为 `1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。


{::comment}
## Decidability
{:/}

## 可决定性

{::comment}
Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).
{:/}

给定两个数，我们可以很直接地决定第一个数是不是小于等于第二个数。我们在此处不给出说明的代码，但我们会在 [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}) 章节重新讨论这个问题。


{::comment}
## Inversion
{:/}

## 反演

{::comment}
In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.
{:/}

在我们的定义中，我们从更小的东西得到更大的东西。例如，我们可以从
`m ≤ n` 得出 `suc m ≤ suc n` 的结论，这里的 `suc m` 比 `m` 更大
（也就是说，前者包含后者），`suc n` 也比 `n` 更大。但有时我们也需要从更大的东西得到更小的东西。

{::comment}
There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{:/}

只有一种方式能够证明对于任意 `m` 和 `n` 有 `suc m ≤ suc n`。这让我们能够反演（invert）之前的规则。

<pre class="Agda">{% raw %}<a id="inv-s≤s"></a><a id="7363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7363" class="Function">inv-s≤s</a> <a id="7371" class="Symbol">:</a> <a id="7373" class="Symbol">∀</a> <a id="7375" class="Symbol">{</a><a id="7376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7376" class="Bound">m</a> <a id="7378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7378" class="Bound">n</a> <a id="7380" class="Symbol">:</a> <a id="7382" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7383" class="Symbol">}</a>
  <a id="7387" class="Symbol">→</a> <a id="7389" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7376" class="Bound">m</a> <a id="7395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="7397" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7378" class="Bound">n</a>
    <a id="7407" class="Comment">-------------</a>
  <a id="7423" class="Symbol">→</a> <a id="7425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7376" class="Bound">m</a> <a id="7427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="7429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7378" class="Bound">n</a>
<a id="7431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7363" class="Function">inv-s≤s</a> <a id="7439" class="Symbol">(</a><a id="7440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="7444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7444" class="Bound">m≤n</a><a id="7447" class="Symbol">)</a> <a id="7449" class="Symbol">=</a> <a id="7451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7444" class="Bound">m≤n</a>{% endraw %}</pre>

{::comment}
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.
{:/}

并不是所有规则都可以反演。实际上，`z≤n` 的规则没有非隐式的假设，因此它没有可以被反演的规则。但这种反演通常是成立的。

{::comment}
Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{:/}

反演的另一个例子是证明只存在一种情况使得一个数字能够小于或等于零。

<pre class="Agda">{% raw %}<a id="inv-z≤n"></a><a id="7886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7886" class="Function">inv-z≤n</a> <a id="7894" class="Symbol">:</a> <a id="7896" class="Symbol">∀</a> <a id="7898" class="Symbol">{</a><a id="7899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7899" class="Bound">m</a> <a id="7901" class="Symbol">:</a> <a id="7903" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7904" class="Symbol">}</a>
  <a id="7908" class="Symbol">→</a> <a id="7910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7899" class="Bound">m</a> <a id="7912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="7914" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
    <a id="7923" class="Comment">--------</a>
  <a id="7934" class="Symbol">→</a> <a id="7936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7899" class="Bound">m</a> <a id="7938" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7940" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
<a id="7945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7886" class="Function">inv-z≤n</a> <a id="7953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a> <a id="7957" class="Symbol">=</a> <a id="7959" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

{::comment}
## Properties of ordering relations
{:/}

## 序关系的性质
{::comment}
Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.
{:/}

数学家对于关系的常见性质给出了约定的名称。

* **自反（Reflexive）**：对于所有的 `n`，关系 `n ≤ n` 成立。
* **传递（Transitive）**：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* **反对称（Anti-symmetric）**：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* **完全（Total）**：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

{::comment}
The relation `_≤_` satisfies all four of these properties.
{:/}

`_≤_` 关系满足上述四条性质。

{::comment}
There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.
{:/}

对于上述性质的组合也有约定的名称。

* **预序（Preorder）**：满足自反和传递的关系。
* **偏序（Partial Order）**：满足反对称的预序。
* **全序（Total Order）**：满足完全的偏序。

{::comment}
If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.
{:/}

如果你进入了关于关系的聚会，你现在知道怎么样和人讨论了，可以讨论关于自反、传递、反对称和完全，或者问一问这是不是预序、偏序或者全序。

{::comment}
Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.
{:/}

更认真的来说，如果你在阅读论文时碰到了一个关系，本文的介绍让你可以对关系有基本的了解和判断，来判断这个关系是不是预序、偏序或者全序。一个认真的作者一般会在文章指出这个关系具有（或者缺少）
上述性质，比如说指出新定义的关系是一个偏序而不是全序。

{::comment}
#### Exercise `orderings` {#orderings}
{:/}

#### 练习 `orderings` {#orderings}

{::comment}
Give an example of a preorder that is not a partial order.
{:/}

给出一个不是偏序的预序的例子。

{::comment}
<pre class="Agda">{% raw %}<a id="10295" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="10348" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>

{::comment}
Give an example of a partial order that is not a total order.
{:/}

给出一个不是全序的偏序的例子。

{::comment}
<pre class="Agda">{% raw %}<a id="10495" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="10548" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Reflexivity
{:/}

## 自反性

{::comment}
The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{:/}

我们第一个来证明的性质是自反性：对于任意自然数 `n`，关系 `n ≤ n` 成立。我们使用标准库的惯例来隐式申明参数，在使用自反性的证明时这样可以更加方便。

<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="10980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10980" class="Function">≤-refl</a> <a id="10987" class="Symbol">:</a> <a id="10989" class="Symbol">∀</a> <a id="10991" class="Symbol">{</a><a id="10992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10992" class="Bound">n</a> <a id="10994" class="Symbol">:</a> <a id="10996" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10997" class="Symbol">}</a>
    <a id="11003" class="Comment">-----</a>
  <a id="11011" class="Symbol">→</a> <a id="11013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10992" class="Bound">n</a> <a id="11015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="11017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10992" class="Bound">n</a>
<a id="11019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10980" class="Function">≤-refl</a> <a id="11026" class="Symbol">{</a><a id="11027" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="11031" class="Symbol">}</a> <a id="11033" class="Symbol">=</a> <a id="11035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="11039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10980" class="Function">≤-refl</a> <a id="11046" class="Symbol">{</a><a id="11047" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11051" class="Bound">n</a><a id="11052" class="Symbol">}</a> <a id="11054" class="Symbol">=</a> <a id="11056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="11060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10980" class="Function">≤-refl</a>{% endraw %}</pre>

{::comment}
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.
{:/}

这个证明直接在 `n` 上进行归纳。在起始步骤中，`zero ≤ zero` 由 `z≤n` 证明；在归纳步骤中，归纳假设 `≤-refl {n}` 给我们带来了 `n ≤ n` 的证明，我们只需要使用 `s≤s`，就可以获得
`suc n ≤ suc n` 的证明。

{::comment}
It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

在 Emacs 中来交互式地证明自反性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Transitivity
{:/}

## 传递性

{::comment}
The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{:/}

我们第二个证明的性质是传递性：对于任意自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ p`
成立，那么 `m ≤ p` 成立。同样，`m`、`n` 和 `p` 是隐式参数：

<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="12099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12099" class="Function">≤-trans</a> <a id="12107" class="Symbol">:</a> <a id="12109" class="Symbol">∀</a> <a id="12111" class="Symbol">{</a><a id="12112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12112" class="Bound">m</a> <a id="12114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12114" class="Bound">n</a> <a id="12116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12116" class="Bound">p</a> <a id="12118" class="Symbol">:</a> <a id="12120" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12121" class="Symbol">}</a>
  <a id="12125" class="Symbol">→</a> <a id="12127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12112" class="Bound">m</a> <a id="12129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="12131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12114" class="Bound">n</a>
  <a id="12135" class="Symbol">→</a> <a id="12137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12114" class="Bound">n</a> <a id="12139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="12141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12116" class="Bound">p</a>
    <a id="12147" class="Comment">-----</a>
  <a id="12155" class="Symbol">→</a> <a id="12157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12112" class="Bound">m</a> <a id="12159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="12161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12116" class="Bound">p</a>
<a id="12163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12099" class="Function">≤-trans</a> <a id="12171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>       <a id="12181" class="Symbol">_</a>          <a id="12192" class="Symbol">=</a>  <a id="12195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="12199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12099" class="Function">≤-trans</a> <a id="12207" class="Symbol">(</a><a id="12208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="12212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12212" class="Bound">m≤n</a><a id="12215" class="Symbol">)</a> <a id="12217" class="Symbol">(</a><a id="12218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="12222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12222" class="Bound">n≤p</a><a id="12225" class="Symbol">)</a>  <a id="12228" class="Symbol">=</a>  <a id="12231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="12235" class="Symbol">(</a><a id="12236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12099" class="Function">≤-trans</a> <a id="12244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12212" class="Bound">m≤n</a> <a id="12248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12222" class="Bound">n≤p</a><a id="12251" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.
{:/}

这里我们在 `m ≤ n` 的**证据（Evidence）**上进行归纳。在起始步骤里，第一个不等式因为 `z≤n` 而成立，那么结论亦可由 `z≤n` 而得出。在这里，`n ≤ p` 的证明是不需要的，我们用 `_` 来表示这个证明没有被使用。

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.
{:/}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个不等式因为 `s≤s n≤p` 而成立，所以我们已知 `suc m ≤ suc n` 和 `suc n ≤ suc p`，求证 `suc m ≤ suc p`。通过归纳假设 `≤-trans m≤n n≤p`，我们得知 `m ≤ p`，在此之上使用 `s≤s` 即可证。

{::comment}
The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.
{:/}

`≤-trans (s≤s m≤n) z≤n` 不可能发生，因为第一个不等式告诉我们中间的数是一个 `suc n`，而第二个不等式告诉我们中间的书是 `zero`。Agda 可以推断这样的情况不可能发现，所以我们不需要
（也不可以）列出这种情况。

{::comment}
Alternatively, we could make the implicit parameters explicit:
{:/}

我们也可以将隐式参数显式地声明。

<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="13741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13741" class="Function">≤-trans′</a> <a id="13750" class="Symbol">:</a> <a id="13752" class="Symbol">∀</a> <a id="13754" class="Symbol">(</a><a id="13755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13755" class="Bound">m</a> <a id="13757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13757" class="Bound">n</a> <a id="13759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13759" class="Bound">p</a> <a id="13761" class="Symbol">:</a> <a id="13763" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13764" class="Symbol">)</a>
  <a id="13768" class="Symbol">→</a> <a id="13770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13755" class="Bound">m</a> <a id="13772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="13774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13757" class="Bound">n</a>
  <a id="13778" class="Symbol">→</a> <a id="13780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13757" class="Bound">n</a> <a id="13782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="13784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13759" class="Bound">p</a>
    <a id="13790" class="Comment">-----</a>
  <a id="13798" class="Symbol">→</a> <a id="13800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13755" class="Bound">m</a> <a id="13802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="13804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13759" class="Bound">p</a>
<a id="13806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13741" class="Function">≤-trans′</a> <a id="13815" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13823" class="Symbol">_</a>       <a id="13831" class="Symbol">_</a>       <a id="13839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>       <a id="13849" class="Symbol">_</a>          <a id="13860" class="Symbol">=</a>  <a id="13863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="13867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13741" class="Function">≤-trans′</a> <a id="13876" class="Symbol">(</a><a id="13877" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13881" class="Bound">m</a><a id="13882" class="Symbol">)</a> <a id="13884" class="Symbol">(</a><a id="13885" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13889" class="Bound">n</a><a id="13890" class="Symbol">)</a> <a id="13892" class="Symbol">(</a><a id="13893" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13897" class="Bound">p</a><a id="13898" class="Symbol">)</a> <a id="13900" class="Symbol">(</a><a id="13901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="13905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13905" class="Bound">m≤n</a><a id="13908" class="Symbol">)</a> <a id="13910" class="Symbol">(</a><a id="13911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="13915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13915" class="Bound">n≤p</a><a id="13918" class="Symbol">)</a>  <a id="13921" class="Symbol">=</a>  <a id="13924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="13928" class="Symbol">(</a><a id="13929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13741" class="Function">≤-trans′</a> <a id="13938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13881" class="Bound">m</a> <a id="13940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13889" class="Bound">n</a> <a id="13942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13897" class="Bound">p</a> <a id="13944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13905" class="Bound">m≤n</a> <a id="13948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13915" class="Bound">n≤p</a><a id="13951" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.
{:/}

有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。我们一般选择使用简短的证明。

{::comment}
The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.
{:/}

对于性质成立证明进行的归纳（如上文中对于 `m ≤ n` 的证明进行归纳），相比于对于性质成立的值进行的归纳
（如对于 `m` 进行归纳），有非常大的价值。我们会经常使用这样的方法。

{::comment}
Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

同样，在 Emacs 中来交互式地证明传递性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Anti-symmetry
{:/}

## 反对称性

{::comment}
The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{:/}

我们证明的第三个性质是反对称性：对于所有的自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
同时成立，那么 `m ≡ n` 成立：

<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="15110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15110" class="Function">≤-antisym</a> <a id="15120" class="Symbol">:</a> <a id="15122" class="Symbol">∀</a> <a id="15124" class="Symbol">{</a><a id="15125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15125" class="Bound">m</a> <a id="15127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15127" class="Bound">n</a> <a id="15129" class="Symbol">:</a> <a id="15131" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15132" class="Symbol">}</a>
  <a id="15136" class="Symbol">→</a> <a id="15138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15125" class="Bound">m</a> <a id="15140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="15142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15127" class="Bound">n</a>
  <a id="15146" class="Symbol">→</a> <a id="15148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15127" class="Bound">n</a> <a id="15150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="15152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15125" class="Bound">m</a>
    <a id="15158" class="Comment">-----</a>
  <a id="15166" class="Symbol">→</a> <a id="15168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15125" class="Bound">m</a> <a id="15170" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="15172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15127" class="Bound">n</a>
<a id="15174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15110" class="Function">≤-antisym</a> <a id="15184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>       <a id="15194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>        <a id="15205" class="Symbol">=</a>  <a id="15208" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="15213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15110" class="Function">≤-antisym</a> <a id="15223" class="Symbol">(</a><a id="15224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="15228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15228" class="Bound">m≤n</a><a id="15231" class="Symbol">)</a> <a id="15233" class="Symbol">(</a><a id="15234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="15238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15238" class="Bound">n≤m</a><a id="15241" class="Symbol">)</a>  <a id="15244" class="Symbol">=</a>  <a id="15247" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="15252" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15256" class="Symbol">(</a><a id="15257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15110" class="Function">≤-antisym</a> <a id="15267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15228" class="Bound">m≤n</a> <a id="15271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15238" class="Bound">n≤m</a><a id="15274" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.
{:/}

同样，我们对于 `m ≤ n` 和 `n ≤ m` 的证明进行归纳。

{::comment}
In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)
{:/}

在起始步骤中，两个不等式都因为 `z≤n` 而成立。因此我们已知 `zero ≤ zero` 和 `zero ≤ zero`，求证 `zero ≡ zero`，由自反性可证。（注：由等式的自反性可证，而不是不等式的自反性）

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.
{::comment}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个等式因为 `s≤s n≤m` 而成立。因此我们已知
`suc m ≤ suc n` 和 `suc n ≤ suc m`，求证 `suc m ≡ suc n`。归纳假设 `≤-antisym m≤n n≤m`
可以证明 `m ≡ n`，因此我们可以使用同余性完成证明。


{::comment}
#### Exercise `≤-antisym-cases` {#leq-antisym-cases}
{:/}

#### 练习 `≤-antisym-cases` {#leq-antisym-cases}

{::comment}
The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?
{:/}

上面的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？

{::comment}
<pre class="Agda">{% raw %}<a id="16609" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="16662" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Total
{:/}

## 完全性

{::comment}
The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
{:/}

我们证明的第四个性质是完全性：对于任何自然数 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。在 `m` 和 `n` 相等时，两者同时成立。

{::comment}
We specify what it means for inequality to be total:
{:/}

我们首先来说明怎么样不等式才是完全的：

<pre class="Agda">{% raw %}<a id="17084" class="Keyword">data</a> <a id="Total"></a><a id="17089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="17095" class="Symbol">(</a><a id="17096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">m</a> <a id="17098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">n</a> <a id="17100" class="Symbol">:</a> <a id="17102" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17103" class="Symbol">)</a> <a id="17105" class="Symbol">:</a> <a id="17107" class="PrimitiveType">Set</a> <a id="17111" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="17120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="17128" class="Symbol">:</a>
      <a id="17136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">m</a> <a id="17138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="17140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">n</a>
      <a id="17148" class="Comment">---------</a>
    <a id="17162" class="Symbol">→</a> <a id="17164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="17170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">m</a> <a id="17172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="17177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="17185" class="Symbol">:</a>
      <a id="17193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">n</a> <a id="17195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="17197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">m</a>
      <a id="17205" class="Comment">---------</a>
    <a id="17219" class="Symbol">→</a> <a id="17221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="17227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">m</a> <a id="17229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">n</a>{% endraw %}</pre>

{::comment}
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.
{:/}

`Total m n` 成立的证明有两种形式：`forward m≤n` 或者 `flipped n≤m`，其中
`m≤n` 和 `n≤m` 分别是 `m ≤ n` 和 `n ≤ m` 的证明。

{::comment}
(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)
{:/}

（如果你对于逻辑学有所了解，上面的定义可以由析取（Disjunction）表示。我们会在 [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}) 章节介绍析取。）

{::comment}
This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{:/}

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：

<pre class="Agda">{% raw %}<a id="18012" class="Keyword">data</a> <a id="Total′"></a><a id="18017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18017" class="Datatype">Total′</a> <a id="18024" class="Symbol">:</a> <a id="18026" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18028" class="Symbol">→</a> <a id="18030" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18032" class="Symbol">→</a> <a id="18034" class="PrimitiveType">Set</a> <a id="18038" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="18047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18047" class="InductiveConstructor">forward′</a> <a id="18056" class="Symbol">:</a> <a id="18058" class="Symbol">∀</a> <a id="18060" class="Symbol">{</a><a id="18061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18061" class="Bound">m</a> <a id="18063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18063" class="Bound">n</a> <a id="18065" class="Symbol">:</a> <a id="18067" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18068" class="Symbol">}</a>
    <a id="18074" class="Symbol">→</a> <a id="18076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18061" class="Bound">m</a> <a id="18078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="18080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18063" class="Bound">n</a>
      <a id="18088" class="Comment">----------</a>
    <a id="18103" class="Symbol">→</a> <a id="18105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18017" class="Datatype">Total′</a> <a id="18112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18061" class="Bound">m</a> <a id="18114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18063" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="18119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18119" class="InductiveConstructor">flipped′</a> <a id="18128" class="Symbol">:</a> <a id="18130" class="Symbol">∀</a> <a id="18132" class="Symbol">{</a><a id="18133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18133" class="Bound">m</a> <a id="18135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18135" class="Bound">n</a> <a id="18137" class="Symbol">:</a> <a id="18139" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18140" class="Symbol">}</a>
    <a id="18146" class="Symbol">→</a> <a id="18148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18135" class="Bound">n</a> <a id="18150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="18152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18133" class="Bound">m</a>
      <a id="18160" class="Comment">----------</a>
    <a id="18175" class="Symbol">→</a> <a id="18177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18017" class="Datatype">Total′</a> <a id="18184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18133" class="Bound">m</a> <a id="18186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18135" class="Bound">n</a>{% endraw %}</pre>

{::comment}
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.
{:/}

类型里的每个参数都转换成构造器的一个隐式参数。索引数据类型中的索引可以变化，正如在
`zero ≤ n` 和 `suc m ≤ suc n` 中那样，而参数化数据类型不一样，其参数必须保持相同，正如在 `Total m n` 中那样。参数化的声明更短，更易于阅读，而且有时可以帮助到 Agda 的终结检查器，所以我们尽可能地使用它们，而不是索引数据类型。

{::comment}
With that preliminary out of the way, we specify and prove totality:
{:/}

在上述准备工作完成后，我们定义并证明完全性。

<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="18962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18962" class="Function">≤-total</a> <a id="18970" class="Symbol">:</a> <a id="18972" class="Symbol">∀</a> <a id="18974" class="Symbol">(</a><a id="18975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18975" class="Bound">m</a> <a id="18977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18977" class="Bound">n</a> <a id="18979" class="Symbol">:</a> <a id="18981" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18982" class="Symbol">)</a> <a id="18984" class="Symbol">→</a> <a id="18986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="18992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18975" class="Bound">m</a> <a id="18994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18977" class="Bound">n</a>
<a id="18996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18962" class="Function">≤-total</a> <a id="19004" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="19012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19012" class="Bound">n</a>                         <a id="19038" class="Symbol">=</a>  <a id="19041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="19049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="19053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18962" class="Function">≤-total</a> <a id="19061" class="Symbol">(</a><a id="19062" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19066" class="Bound">m</a><a id="19067" class="Symbol">)</a> <a id="19069" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="19095" class="Symbol">=</a>  <a id="19098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="19106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="19110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18962" class="Function">≤-total</a> <a id="19118" class="Symbol">(</a><a id="19119" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19123" class="Bound">m</a><a id="19124" class="Symbol">)</a> <a id="19126" class="Symbol">(</a><a id="19127" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19131" class="Bound">n</a><a id="19132" class="Symbol">)</a> <a id="19134" class="Keyword">with</a> <a id="19139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18962" class="Function">≤-total</a> <a id="19147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19123" class="Bound">m</a> <a id="19149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19131" class="Bound">n</a>
<a id="19151" class="Symbol">...</a>                        <a id="19178" class="Symbol">|</a> <a id="19180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="19188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19188" class="Bound">m≤n</a>  <a id="19193" class="Symbol">=</a>  <a id="19196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="19204" class="Symbol">(</a><a id="19205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="19209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19188" class="Bound">m≤n</a><a id="19212" class="Symbol">)</a>
<a id="19214" class="Symbol">...</a>                        <a id="19241" class="Symbol">|</a> <a id="19243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="19251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19251" class="Bound">n≤m</a>  <a id="19256" class="Symbol">=</a>  <a id="19259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="19267" class="Symbol">(</a><a id="19268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="19272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19251" class="Bound">n≤m</a><a id="19275" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.
{:/}

这里，我们的证明在两个参数上进行归纳，并按照情况分析：

* **第一起始步骤**：如果第一个参数是 `zero`，第二个参数是 `n`，那么 forward
  条件成立，我们使用 `z≤n` 作为 `zero ≤ n` 的证明。

* **第二起始步骤**：如果第一个参数是 `suc m`，第二个参数是 `zero`，那么 flipped
  条件成立，我们使用 `z≤n` 作为 `zero ≤ suc m` 的证明。

* **归纳步骤**：如果第一个参数是 `suc m`，第二个参数是 `suc n`，那么归纳假设
  `≤-total m n` 可以给出如下推断：

  + 归纳假设的 forward 条件成立，以 `m≤n` 作为 `m ≤ n` 的证明。以此我们可以使用
    `s≤s m≤n` 作为 `suc m ≤ suc n` 来证明 forward 条件成立。

  + 归纳假设的 flipped 条件成立，以 `n≤m` 作为 `n ≤ m` 的证明。以此我们可以使用
    `s≤s n≤m` 作为 `suc n ≤ suc m` 来证明 flipped 条件成立。

{::comment}
This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.
{:/}

这是我们第一次在 Agda 中使用 `with` 语句。`with` 关键字后面有一个表达式和一或多行。每行以省略号（`...`）和一个竖线（`|`）开头，后面跟着用来匹配表达式的模式，和等式的右手边。

{::comment}
Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{:/}

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：

<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="21488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21488" class="Function">≤-total′</a> <a id="21497" class="Symbol">:</a> <a id="21499" class="Symbol">∀</a> <a id="21501" class="Symbol">(</a><a id="21502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21502" class="Bound">m</a> <a id="21504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21504" class="Bound">n</a> <a id="21506" class="Symbol">:</a> <a id="21508" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21509" class="Symbol">)</a> <a id="21511" class="Symbol">→</a> <a id="21513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="21519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21502" class="Bound">m</a> <a id="21521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21504" class="Bound">n</a>
<a id="21523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21488" class="Function">≤-total′</a> <a id="21532" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="21540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21540" class="Bound">n</a>        <a id="21549" class="Symbol">=</a>  <a id="21552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="21560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="21564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21488" class="Function">≤-total′</a> <a id="21573" class="Symbol">(</a><a id="21574" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21578" class="Bound">m</a><a id="21579" class="Symbol">)</a> <a id="21581" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="21590" class="Symbol">=</a>  <a id="21593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="21601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="21605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21488" class="Function">≤-total′</a> <a id="21614" class="Symbol">(</a><a id="21615" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21619" class="Bound">m</a><a id="21620" class="Symbol">)</a> <a id="21622" class="Symbol">(</a><a id="21623" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21627" class="Bound">n</a><a id="21628" class="Symbol">)</a>  <a id="21631" class="Symbol">=</a>  <a id="21634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21666" class="Function">helper</a> <a id="21641" class="Symbol">(</a><a id="21642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21488" class="Function">≤-total′</a> <a id="21651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21619" class="Bound">m</a> <a id="21653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21627" class="Bound">n</a><a id="21654" class="Symbol">)</a>
  <a id="21658" class="Keyword">where</a>
  <a id="21666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21666" class="Function">helper</a> <a id="21673" class="Symbol">:</a> <a id="21675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="21681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21619" class="Bound">m</a> <a id="21683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21627" class="Bound">n</a> <a id="21685" class="Symbol">→</a> <a id="21687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="21693" class="Symbol">(</a><a id="21694" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21619" class="Bound">m</a><a id="21699" class="Symbol">)</a> <a id="21701" class="Symbol">(</a><a id="21702" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21627" class="Bound">n</a><a id="21707" class="Symbol">)</a>
  <a id="21711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21666" class="Function">helper</a> <a id="21718" class="Symbol">(</a><a id="21719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="21727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21727" class="Bound">m≤n</a><a id="21730" class="Symbol">)</a>  <a id="21733" class="Symbol">=</a>  <a id="21736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="21744" class="Symbol">(</a><a id="21745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="21749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21727" class="Bound">m≤n</a><a id="21752" class="Symbol">)</a>
  <a id="21756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21666" class="Function">helper</a> <a id="21763" class="Symbol">(</a><a id="21764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="21772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21772" class="Bound">n≤m</a><a id="21775" class="Symbol">)</a>  <a id="21778" class="Symbol">=</a>  <a id="21781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="21789" class="Symbol">(</a><a id="21790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="21794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21772" class="Bound">n≤m</a><a id="21797" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.
{:/}

这也是我们第一次在 Agda 中使用 `where` 语句。`where` 关键字后面有一或多条定义，其必须被缩进。之前等式左手边的约束变量（此例中的 `m` 和 `n`）在嵌套的定义中仍然在作用域内。在嵌套定义中的约束标识符（此例中的 `helper` ）在等式的右手边的作用域内。

{::comment}
If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{:/}

如果两个参数相同，那么两个情况同时成立，我们可以返回任一证明。上面的代码中我们返回 forward 条件，但是我们也可以返回 flipped 条件，如下：

<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="22697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22697" class="Function">≤-total″</a> <a id="22706" class="Symbol">:</a> <a id="22708" class="Symbol">∀</a> <a id="22710" class="Symbol">(</a><a id="22711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22711" class="Bound">m</a> <a id="22713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22713" class="Bound">n</a> <a id="22715" class="Symbol">:</a> <a id="22717" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22718" class="Symbol">)</a> <a id="22720" class="Symbol">→</a> <a id="22722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17089" class="Datatype">Total</a> <a id="22728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22711" class="Bound">m</a> <a id="22730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22713" class="Bound">n</a>
<a id="22732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22697" class="Function">≤-total″</a> <a id="22741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22741" class="Bound">m</a>       <a id="22749" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="22775" class="Symbol">=</a>  <a id="22778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="22786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="22790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22697" class="Function">≤-total″</a> <a id="22799" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="22807" class="Symbol">(</a><a id="22808" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="22812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22812" class="Bound">n</a><a id="22813" class="Symbol">)</a>                   <a id="22833" class="Symbol">=</a>  <a id="22836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="22844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1528" class="InductiveConstructor">z≤n</a>
<a id="22848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22697" class="Function">≤-total″</a> <a id="22857" class="Symbol">(</a><a id="22858" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="22862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22862" class="Bound">m</a><a id="22863" class="Symbol">)</a> <a id="22865" class="Symbol">(</a><a id="22866" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="22870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22870" class="Bound">n</a><a id="22871" class="Symbol">)</a> <a id="22873" class="Keyword">with</a> <a id="22878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22697" class="Function">≤-total″</a> <a id="22887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22862" class="Bound">m</a> <a id="22889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22870" class="Bound">n</a>
<a id="22891" class="Symbol">...</a>                        <a id="22918" class="Symbol">|</a> <a id="22920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="22928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22928" class="Bound">m≤n</a>   <a id="22934" class="Symbol">=</a>  <a id="22937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17120" class="InductiveConstructor">forward</a> <a id="22945" class="Symbol">(</a><a id="22946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="22950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22928" class="Bound">m≤n</a><a id="22953" class="Symbol">)</a>
<a id="22955" class="Symbol">...</a>                        <a id="22982" class="Symbol">|</a> <a id="22984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="22992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22992" class="Bound">n≤m</a>   <a id="22998" class="Symbol">=</a>  <a id="23001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17177" class="InductiveConstructor">flipped</a> <a id="23009" class="Symbol">(</a><a id="23010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="23014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22992" class="Bound">n≤m</a><a id="23017" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
It differs from the original code in that it pattern
matches on the second argument before the first argument.
{:/}

两者的区别在于上述代码在对于第一个参数进行模式匹配之前先对于第二个参数先进行模式匹配。


{::comment}
## Monotonicity
{:/}

## 单调性

{::comment}
If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:
{:/}

如果在聚会中碰到了一个运算符和一个序，那么有人可能会问这个运算符对于这个序是不是
**单调的（Monotonic）**。比如说，加法对于小于等于是单调的，这意味着：

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

{::comment}
The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{:/}

这个证明可以用我们学会的方法，很直接的来完成。我们最好把它分成三个部分，首先我们证明加法对于小于等于在右手边是单调的：

<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="23891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="23901" class="Symbol">:</a> <a id="23903" class="Symbol">∀</a> <a id="23905" class="Symbol">(</a><a id="23906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23906" class="Bound">n</a> <a id="23908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23908" class="Bound">p</a> <a id="23910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23910" class="Bound">q</a> <a id="23912" class="Symbol">:</a> <a id="23914" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="23915" class="Symbol">)</a>
  <a id="23919" class="Symbol">→</a> <a id="23921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23908" class="Bound">p</a> <a id="23923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="23925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23910" class="Bound">q</a>
    <a id="23931" class="Comment">-------------</a>
  <a id="23947" class="Symbol">→</a> <a id="23949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23906" class="Bound">n</a> <a id="23951" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23908" class="Bound">p</a> <a id="23955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="23957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23906" class="Bound">n</a> <a id="23959" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23910" class="Bound">q</a>
<a id="23963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="23973" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="23981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23981" class="Bound">p</a> <a id="23983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23983" class="Bound">q</a> <a id="23985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23985" class="Bound">p≤q</a>  <a id="23990" class="Symbol">=</a>  <a id="23993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23985" class="Bound">p≤q</a>
<a id="23997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="24007" class="Symbol">(</a><a id="24008" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="24012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24012" class="Bound">n</a><a id="24013" class="Symbol">)</a> <a id="24015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24015" class="Bound">p</a> <a id="24017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24017" class="Bound">q</a> <a id="24019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24019" class="Bound">p≤q</a>  <a id="24024" class="Symbol">=</a>  <a id="24027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1577" class="InductiveConstructor">s≤s</a> <a id="24031" class="Symbol">(</a><a id="24032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="24042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24012" class="Bound">n</a> <a id="24044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24015" class="Bound">p</a> <a id="24046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24017" class="Bound">q</a> <a id="24048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24019" class="Bound">p≤q</a><a id="24051" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.
{:/}

我们对于第一个参数进行归纳。

* **起始步骤**：第一个参数是 `zero`，那么 `zero + p ≤ zero + q` 可以化简为 `p ≤ q`，
  其证明由 `p≤q` 给出。

* **归纳步骤**：第一个参数是 `suc n`，那么 `suc n + p ≤ suc n + q` 可以化简为
  `suc (n + p) ≤ suc (n + q)`。归纳假设 `+-monoʳ-≤ n p q p≤q` 可以证明
  `n + p ≤ n + q`，我们在此之上使用 `s≤s` 即可得证。

{::comment}
Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{:/}

接下来，我们证明加法对于小于等于在左手边是单调的。我们可以用之前的结论和加法的交换律来证明：

<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="25051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25051" class="Function">+-monoˡ-≤</a> <a id="25061" class="Symbol">:</a> <a id="25063" class="Symbol">∀</a> <a id="25065" class="Symbol">(</a><a id="25066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25066" class="Bound">m</a> <a id="25068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25068" class="Bound">n</a> <a id="25070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25070" class="Bound">p</a> <a id="25072" class="Symbol">:</a> <a id="25074" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="25075" class="Symbol">)</a>
  <a id="25079" class="Symbol">→</a> <a id="25081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25066" class="Bound">m</a> <a id="25083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="25085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25068" class="Bound">n</a>
    <a id="25091" class="Comment">-------------</a>
  <a id="25107" class="Symbol">→</a> <a id="25109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25066" class="Bound">m</a> <a id="25111" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25070" class="Bound">p</a> <a id="25115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="25117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25068" class="Bound">n</a> <a id="25119" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25070" class="Bound">p</a>
<a id="25123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25051" class="Function">+-monoˡ-≤</a> <a id="25133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25133" class="Bound">m</a> <a id="25135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25135" class="Bound">n</a> <a id="25137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25137" class="Bound">p</a> <a id="25139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25139" class="Bound">m≤n</a>  <a id="25144" class="Keyword">rewrite</a> <a id="25152" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="25159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25133" class="Bound">m</a> <a id="25161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25137" class="Bound">p</a> <a id="25163" class="Symbol">|</a> <a id="25165" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="25172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25135" class="Bound">n</a> <a id="25174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25137" class="Bound">p</a>  <a id="25177" class="Symbol">=</a> <a id="25179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="25189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25137" class="Bound">p</a> <a id="25191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25133" class="Bound">m</a> <a id="25193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25135" class="Bound">n</a> <a id="25195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25139" class="Bound">m≤n</a>{% endraw %}</pre>

{::comment}
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.
{:/}

用 `+-comm m p` 和 `+-comm n p` 来重写，可以让 `m + p ≤ n + p` 转换成 `p + n ≤ p + m`，而我们可以用 `+-moroʳ-≤ p m n m≤n` 来证明。

{::comment}
Third, we combine the two previous results:
{:/}

最后，我们把前两步的结论结合起来：

<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="25574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25574" class="Function">+-mono-≤</a> <a id="25583" class="Symbol">:</a> <a id="25585" class="Symbol">∀</a> <a id="25587" class="Symbol">(</a><a id="25588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25588" class="Bound">m</a> <a id="25590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25590" class="Bound">n</a> <a id="25592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25592" class="Bound">p</a> <a id="25594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25594" class="Bound">q</a> <a id="25596" class="Symbol">:</a> <a id="25598" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="25599" class="Symbol">)</a>
  <a id="25603" class="Symbol">→</a> <a id="25605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25588" class="Bound">m</a> <a id="25607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="25609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25590" class="Bound">n</a>
  <a id="25613" class="Symbol">→</a> <a id="25615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25592" class="Bound">p</a> <a id="25617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="25619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25594" class="Bound">q</a>
    <a id="25625" class="Comment">-------------</a>
  <a id="25641" class="Symbol">→</a> <a id="25643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25588" class="Bound">m</a> <a id="25645" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25592" class="Bound">p</a> <a id="25649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Datatype Operator">≤</a> <a id="25651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25590" class="Bound">n</a> <a id="25653" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="25655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25594" class="Bound">q</a>
<a id="25657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25574" class="Function">+-mono-≤</a> <a id="25666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25666" class="Bound">m</a> <a id="25668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25668" class="Bound">n</a> <a id="25670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25670" class="Bound">p</a> <a id="25672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25672" class="Bound">q</a> <a id="25674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25674" class="Bound">m≤n</a> <a id="25678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25678" class="Bound">p≤q</a>  <a id="25683" class="Symbol">=</a>  <a id="25686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12099" class="Function">≤-trans</a> <a id="25694" class="Symbol">(</a><a id="25695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25051" class="Function">+-monoˡ-≤</a> <a id="25705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25666" class="Bound">m</a> <a id="25707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25668" class="Bound">n</a> <a id="25709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25670" class="Bound">p</a> <a id="25711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25674" class="Bound">m≤n</a><a id="25714" class="Symbol">)</a> <a id="25716" class="Symbol">(</a><a id="25717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23891" class="Function">+-monoʳ-≤</a> <a id="25727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25668" class="Bound">n</a> <a id="25729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25670" class="Bound">p</a> <a id="25731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25672" class="Bound">q</a> <a id="25733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25678" class="Bound">p≤q</a><a id="25736" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.
{:/}

使用 `+-monoˡ-≤ m n p m≤n` 可以证明 `m + p ≤ n + p`，使用 `+-monoʳ-≤ n p q p≤q` 可以证明 `n + p ≤ n + q`，用传递性把两者连接起来，我们可以获得 `m + p ≤ n + q` 的证明，如上所示。

{::comment}
#### Exercise `*-mono-≤` (stretch)
{:/}

#### 练习 `*-mono-≤` （延伸）

{::comment}
Show that multiplication is monotonic with regard to inequality.
{:/}

证明乘法对于小于等于是单调的。

{::comment}
<pre class="Agda">{% raw %}<a id="26306" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="26359" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Strict inequality {#strict-inequality}
{:/}

## 严格不等关系 {#strict-inequality}

{::comment}
We can define strict inequality similarly to inequality:
{:/}

我们可以用类似于定义不等关系的方法来定义严格不等关系。

<pre class="Agda">{% raw %}<a id="26594" class="Keyword">infix</a> <a id="26600" class="Number">4</a> <a id="26602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26612" class="Datatype Operator">_&lt;_</a>

<a id="26607" class="Keyword">data</a> <a id="_&lt;_"></a><a id="26612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26612" class="Datatype Operator">_&lt;_</a> <a id="26616" class="Symbol">:</a> <a id="26618" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="26620" class="Symbol">→</a> <a id="26622" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="26624" class="Symbol">→</a> <a id="26626" class="PrimitiveType">Set</a> <a id="26630" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="26639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26639" class="InductiveConstructor">z&lt;s</a> <a id="26643" class="Symbol">:</a> <a id="26645" class="Symbol">∀</a> <a id="26647" class="Symbol">{</a><a id="26648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26648" class="Bound">n</a> <a id="26650" class="Symbol">:</a> <a id="26652" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="26653" class="Symbol">}</a>
      <a id="26661" class="Comment">------------</a>
    <a id="26678" class="Symbol">→</a> <a id="26680" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="26685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26612" class="Datatype Operator">&lt;</a> <a id="26687" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="26691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26648" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="26696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26696" class="InductiveConstructor">s&lt;s</a> <a id="26700" class="Symbol">:</a> <a id="26702" class="Symbol">∀</a> <a id="26704" class="Symbol">{</a><a id="26705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26705" class="Bound">m</a> <a id="26707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26707" class="Bound">n</a> <a id="26709" class="Symbol">:</a> <a id="26711" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="26712" class="Symbol">}</a>
    <a id="26718" class="Symbol">→</a> <a id="26720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26705" class="Bound">m</a> <a id="26722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26612" class="Datatype Operator">&lt;</a> <a id="26724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26707" class="Bound">n</a>
      <a id="26732" class="Comment">-------------</a>
    <a id="26750" class="Symbol">→</a> <a id="26752" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="26756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26705" class="Bound">m</a> <a id="26758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26612" class="Datatype Operator">&lt;</a> <a id="26760" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="26764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26707" class="Bound">n</a>{% endraw %}</pre>

{::comment}
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.
{:/}

严格不等关系与不等关系最重要的区别在于，0 小于任何数的后继，而不小于 0。

{::comment}
Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.
{:/}

显然，严格不等关系不是自反的，而是**非自反的（Irreflexive）**，表示 `n < n` 对于任何值 `n` 都不成立。和不等关系一样，严格不等关系是传递的。严格不等关系不是完全的，但是满足一个相似的性质：*三分律*（Trichotomy）：对于任意的 `m` 和 `n`，`m < n`、`m ≡ n` 或者
`m > n` 三者有且仅有一者成立。（我们定义 `m > n` 当且仅当 `n < m` 成立时成立）
严格不等关系对于加法和乘法也是单调的。

{::comment}
Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).
{:/}

我们把一部分上述性质作为习题。非自反性需要逻辑非，三分律需要证明三者是互斥的，因此这两个性质暂不做为习题。我们会在 [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}) 章节来重新讨论。

{::comment}
It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.
{:/}

我们可以直接地来证明 `suc m ≤ n` 蕴含了 `m < n`，及其逆命题。因此我们亦可从不等关系的性质中，使用此性质来证明严格不等关系的性质。


{::comment}
#### Exercise `<-trans` (recommended) {#less-trans}
{:/}

#### 练习 `<-trans` （推荐） {#less-trans}

{::comment}
Show that strict inequality is transitive.
{:/}

证明严格不等是传递的。

{::comment}
<pre class="Agda">{% raw %}<a id="28551" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="28604" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `trichotomy` {#trichotomy}
{:/}

#### 练习 `trichotomy` {#trichotomy}

{::comment}
Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.
{:/}

证明严格不等关系满足弱化的三元律，证明对于任意 `m` 和 `n`，下列命题有一条成立：

  * `m < n`，
  * `m ≡ n`，或者
  * `m > n`。

{::comment}
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)
{:/}

定义 `m > n` 为 `n < m`。你需要一个合适的数据类型声明，如同我们在证明完全性中使用的那样。
（我们会在介绍[逻辑非]({{ site.baseurl }}{% link out/plfa/Negation.md%})以后证明三者是互斥的）

{::comment}
<pre class="Agda">{% raw %}<a id="29365" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="29418" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `+-mono-<` {#plus-mono-less}
{:/}

#### 练习 `+-mono-<` {#plus-mono-less}

{::comment}
Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.
{:/}

证明加法对于严格不等关系是单调的。正如不等关系中那样，你可以需要额外的定义。

{::comment}
<pre class="Agda">{% raw %}<a id="29758" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="29811" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}
{:/}

#### 练习 `≤-iff-<` (推荐) {#leq-iff-less}

{::comment}
Show that `suc m ≤ n` implies `m < n`, and conversely.
{:/}

证明 `suc m ≤ n` 蕴含了 `m < n`，及其逆命题。

{::comment}
<pre class="Agda">{% raw %}<a id="30082" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="30135" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `<-trans-revisited` {#less-trans-revisited}
{:/}

#### 练习 `<-trans-revisited` {#less-trans-revisited}

{::comment}
Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.
{:/}

用另外一种方法证明严格不等是传递的，使用之前证明的不等关系和严格不等关系的联系，以及不等关系的传递性。

{::comment}
<pre class="Agda">{% raw %}<a id="30555" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="30608" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Even and odd
{:/}

## 奇和偶

{::comment}
As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{:/}

作为一个额外的例子，我们来定义奇数和偶数。不等关系和严格不等关系是**二元关系**，而奇偶性是**一元关系**，有时也被叫做**谓词（Predicate）**：

<pre class="Agda">{% raw %}<a id="30979" class="Keyword">data</a> <a id="even"></a><a id="30984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="30989" class="Symbol">:</a> <a id="30991" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="30993" class="Symbol">→</a> <a id="30995" class="PrimitiveType">Set</a>
<a id="30999" class="Keyword">data</a> <a id="odd"></a><a id="31004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a>  <a id="31009" class="Symbol">:</a> <a id="31011" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="31013" class="Symbol">→</a> <a id="31015" class="PrimitiveType">Set</a>

<a id="31020" class="Keyword">data</a> <a id="31025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="31030" class="Keyword">where</a>

  <a id="even.zero"></a><a id="31039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31039" class="InductiveConstructor">zero</a> <a id="31044" class="Symbol">:</a>
      <a id="31052" class="Comment">---------</a>
      <a id="31068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="31073" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="31081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31081" class="InductiveConstructor">suc</a>  <a id="31086" class="Symbol">:</a> <a id="31088" class="Symbol">∀</a> <a id="31090" class="Symbol">{</a><a id="31091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31091" class="Bound">n</a> <a id="31093" class="Symbol">:</a> <a id="31095" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="31096" class="Symbol">}</a>
    <a id="31102" class="Symbol">→</a> <a id="31104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a> <a id="31108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31091" class="Bound">n</a>
      <a id="31116" class="Comment">------------</a>
    <a id="31133" class="Symbol">→</a> <a id="31135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="31140" class="Symbol">(</a><a id="31141" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="31145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31091" class="Bound">n</a><a id="31146" class="Symbol">)</a>

<a id="31149" class="Keyword">data</a> <a id="31154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a> <a id="31158" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="31167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31167" class="InductiveConstructor">suc</a>   <a id="31173" class="Symbol">:</a> <a id="31175" class="Symbol">∀</a> <a id="31177" class="Symbol">{</a><a id="31178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31178" class="Bound">n</a> <a id="31180" class="Symbol">:</a> <a id="31182" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="31183" class="Symbol">}</a>
    <a id="31189" class="Symbol">→</a> <a id="31191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="31196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31178" class="Bound">n</a>
      <a id="31204" class="Comment">-----------</a>
    <a id="31220" class="Symbol">→</a> <a id="31222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a> <a id="31226" class="Symbol">(</a><a id="31227" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="31231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31178" class="Bound">n</a><a id="31232" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.
{:/}

一个数是偶数，如果它是 0，或者是奇数的后继。一个数是奇数，如果它是偶数的后继。

{::comment}
This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).
{:/}

这是我们第一次定义一个相互递归的数据类型。因为每个标识符必须在使用前声明，所以我们首先声明索引数据类型 `even` 和 `odd` （省略 `where` 关键字和其构造器的定义），然后声明其构造器（省略其签名 `ℕ → Set`，因为在之前已经给出）。

{::comment}
This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:
{:/}

这也是我们第一次使用 **重载（Overloaded）**的构造器。这意味着不同类型的构造器拥有相同的名字。在这里 `suc` 表示下面三种构造器其中之一：

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

{::comment}
Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.
{:/}

同理，`zero` 表示两种构造器的一种。因为类型推导的限制，Agda 不允许重载已定义的名字，但是允许重载构造器。我们推荐将重载限制在有关联的定义中，如我们所做的这样，但这不是必须的。

{::comment}
We show that the sum of two even numbers is even:
{:/}

我们证明两个偶数之和是偶数：

<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="32862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32862" class="Function">e+e≡e</a> <a id="32868" class="Symbol">:</a> <a id="32870" class="Symbol">∀</a> <a id="32872" class="Symbol">{</a><a id="32873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32873" class="Bound">m</a> <a id="32875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32875" class="Bound">n</a> <a id="32877" class="Symbol">:</a> <a id="32879" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="32880" class="Symbol">}</a>
  <a id="32884" class="Symbol">→</a> <a id="32886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="32891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32873" class="Bound">m</a>
  <a id="32895" class="Symbol">→</a> <a id="32897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="32902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32875" class="Bound">n</a>
    <a id="32908" class="Comment">------------</a>
  <a id="32923" class="Symbol">→</a> <a id="32925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="32930" class="Symbol">(</a><a id="32931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32873" class="Bound">m</a> <a id="32933" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="32935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32875" class="Bound">n</a><a id="32936" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="32939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32939" class="Function">o+e≡o</a> <a id="32945" class="Symbol">:</a> <a id="32947" class="Symbol">∀</a> <a id="32949" class="Symbol">{</a><a id="32950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32950" class="Bound">m</a> <a id="32952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32952" class="Bound">n</a> <a id="32954" class="Symbol">:</a> <a id="32956" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="32957" class="Symbol">}</a>
  <a id="32961" class="Symbol">→</a> <a id="32963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a> <a id="32967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32950" class="Bound">m</a>
  <a id="32971" class="Symbol">→</a> <a id="32973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30984" class="Datatype">even</a> <a id="32978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32952" class="Bound">n</a>
    <a id="32984" class="Comment">-----------</a>
  <a id="32998" class="Symbol">→</a> <a id="33000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31004" class="Datatype">odd</a> <a id="33004" class="Symbol">(</a><a id="33005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32950" class="Bound">m</a> <a id="33007" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="33009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32952" class="Bound">n</a><a id="33010" class="Symbol">)</a>

<a id="33013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32862" class="Function">e+e≡e</a> <a id="33019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31039" class="InductiveConstructor">zero</a>     <a id="33028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33028" class="Bound">en</a>  <a id="33032" class="Symbol">=</a>  <a id="33035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33028" class="Bound">en</a>
<a id="33038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32862" class="Function">e+e≡e</a> <a id="33044" class="Symbol">(</a><a id="33045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31081" class="InductiveConstructor">suc</a> <a id="33049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33049" class="Bound">om</a><a id="33051" class="Symbol">)</a> <a id="33053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33053" class="Bound">en</a>  <a id="33057" class="Symbol">=</a>  <a id="33060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31081" class="InductiveConstructor">suc</a> <a id="33064" class="Symbol">(</a><a id="33065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32939" class="Function">o+e≡o</a> <a id="33071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33049" class="Bound">om</a> <a id="33074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33053" class="Bound">en</a><a id="33076" class="Symbol">)</a>

<a id="33079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32939" class="Function">o+e≡o</a> <a id="33085" class="Symbol">(</a><a id="33086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31167" class="InductiveConstructor">suc</a> <a id="33090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33090" class="Bound">em</a><a id="33092" class="Symbol">)</a> <a id="33094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33094" class="Bound">en</a>  <a id="33098" class="Symbol">=</a>  <a id="33101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#31167" class="InductiveConstructor">suc</a> <a id="33105" class="Symbol">(</a><a id="33106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32862" class="Function">e+e≡e</a> <a id="33112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33090" class="Bound">em</a> <a id="33115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#33094" class="Bound">en</a><a id="33117" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.
{:/}

与相互递归的定义对应，我们用两个相互递归的函数，一个证明两个偶数之和是偶数，另一个证明一个奇数与一个偶数之和是奇数。

{::comment}
This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.
{:/}

这是我们第一次使用相互递归的函数。因为每个标识符必须在使用前声明，我们先给出两个函数的签名，然后再给出其定义。

{::comment}
To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.
{:/}

要证明两个偶数之和为偶，我们考虑第一个数为偶数的证明。如果是因为第一个数为 0，那么第二个数为偶数的证明即为和为偶数的证明。如果是因为第一个数为奇数的后继，那么和为偶数是因为他是一个奇数和一个偶数的和的后续，而这个和是一个奇数。


{::comment}
To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.
{:/}

要证明一个奇数和一个偶数的和是奇数，我们考虑第一个数是奇数的证明。如果是因为它是一个偶数的后继，那么和为奇数，因为它是两个偶数之和的后继，而这个和是一个偶数。


{::comment}
#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}
{:/}

#### 练习 `o+o≡e` (延伸) {#odd-plus-odd}

{::comment}
Show that the sum of two odd numbers is even.
{:/}

证明两个奇数之和为偶数。

{::comment}
<pre class="Agda">{% raw %}<a id="34760" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="34813" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}
{:/}

#### 练习 `Bin-predicates` (延伸) {#Bin-predicates}

{::comment}
Recall that
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:
{:/}

回忆我们在练习 [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin) 中定义了一个数据类型 `Bin` 来用二进制字符串表示自然数。这个表达方法不是唯一的，因为我们在开头加任意个 0。因此，11 可以由以下方法表示：

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

{::comment}
Define a predicate
{:/}

定义一个谓词

    Can : Bin → Set

{::comment}
over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate
{:/}

其在一个二进制字符串的表示是标准的（Canonical）时成立，表示它没有开头的 0。在两个 11 的表达方式中，第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set

{::comment}
that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).
{:/}

其仅在一个二进制字符串开头为 1 时成立。一个二进制字符串是标准的，如果它开头是 1 （表示一个正数），或者它仅是一个 0 （表示 0）。

{::comment}
Show that increment preserves canonical bitstrings:
{:/}

证明递增可以保持标准性。

    Can x
    ------------
    Can (inc x)

{::comment}
Show that converting a natural to a bitstring always yields a
canonical bitstring:
{:/}

证明从自然数转换成的二进制字符串是标准的。

    ----------
    Can (to n)

{::comment}
Show that converting a canonical bitstring to a natural
and back is the identity:
{:/}

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
(Hint: For each of these, you may first need to prove related
properties of `One`.)
{:/}

（提示：对于每一条习题，先从 `One` 的性质开始）

{::comment}
<pre class="Agda">{% raw %}<a id="36706" class="Comment">-- Your code goes here</a>{% endraw %}</pre>
{:/}

<pre class="Agda">{% raw %}<a id="36759" class="Comment">-- 请将代码写在此处。</a>{% endraw %}</pre>


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中有类似于本章介绍的定义：

<pre class="Agda">{% raw %}<a id="36963" class="Keyword">import</a> <a id="36970" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="36979" class="Keyword">using</a> <a id="36985" class="Symbol">(</a><a id="36986" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="36989" class="Symbol">;</a> <a id="36991" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="36994" class="Symbol">;</a> <a id="36996" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="36999" class="Symbol">)</a>
<a id="37001" class="Keyword">import</a> <a id="37008" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="37028" class="Keyword">using</a> <a id="37034" class="Symbol">(</a><a id="37035" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="37041" class="Symbol">;</a> <a id="37043" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="37050" class="Symbol">;</a> <a id="37052" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="37061" class="Symbol">;</a> <a id="37063" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="37070" class="Symbol">;</a>
                                  <a id="37106" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="37115" class="Symbol">;</a> <a id="37117" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="37126" class="Symbol">;</a> <a id="37128" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="37136" class="Symbol">)</a>{% endraw %}</pre>

{::comment}
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.
{:/}

在标准库中，`≤-total` 是使用析取定义的（我们将在 [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}) 章节定义）。
`+-monoʳ-≤`、`+-monoˡ-≤` 和 `+-mono-≤` 的证明方法和本书不同。更多的参数是隐式申明的。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
{:/}

本章使用了如下 Unicode 符号：

    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)

{::comment}
The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
{:/}

`\^l` 和 `\^r` 命令给出了左右箭头，以及上标字母 `l` 和 `r`。
