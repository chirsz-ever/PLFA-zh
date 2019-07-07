---
src       : tspl/PUC-Assignment3.lagda
title     : "PUC-Assignment3: PUC Assignment 3"
layout    : page
permalink : /PUC-Assignment3/
---

<pre class="Agda">{% raw %}<a id="118" class="Keyword">module</a> <a id="125" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}" class="Module">PUC-Assignment3</a> <a id="141" class="Keyword">where</a>{% endraw %}</pre>

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

<pre class="Agda">{% raw %}<a id="583" class="Keyword">import</a> <a id="590" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="628" class="Symbol">as</a> <a id="631" class="Module">Eq</a>
<a id="634" class="Keyword">open</a> <a id="639" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="642" class="Keyword">using</a> <a id="648" class="Symbol">(</a><a id="649" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="652" class="Symbol">;</a> <a id="654" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="658" class="Symbol">;</a> <a id="660" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="664" class="Symbol">;</a> <a id="666" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="669" class="Symbol">)</a>
<a id="671" class="Keyword">open</a> <a id="676" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a> <a id="691" class="Keyword">using</a> <a id="697" class="Symbol">(</a><a id="698" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin_</a><a id="704" class="Symbol">;</a> <a id="706" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">_≡⟨⟩_</a><a id="711" class="Symbol">;</a> <a id="713" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">_≡⟨_⟩_</a><a id="719" class="Symbol">;</a> <a id="721" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">_∎</a><a id="723" class="Symbol">)</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="https://agda.github.io/agda-stdlib/v0.17/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="752" class="Keyword">using</a> <a id="758" class="Symbol">(</a><a id="759" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Bool.html#67" class="Datatype">Bool</a><a id="763" class="Symbol">;</a> <a id="765" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Bool.html#92" class="InductiveConstructor">true</a><a id="769" class="Symbol">;</a> <a id="771" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Bool.html#86" class="InductiveConstructor">false</a><a id="776" class="Symbol">;</a> <a id="778" href="https://agda.github.io/agda-stdlib/v0.17/Data.Bool.Base.html#864" class="Function">T</a><a id="779" class="Symbol">;</a> <a id="781" href="https://agda.github.io/agda-stdlib/v0.17/Data.Bool.Base.html#1012" class="Function Operator">_∧_</a><a id="784" class="Symbol">;</a> <a id="786" href="https://agda.github.io/agda-stdlib/v0.17/Data.Bool.Base.html#1070" class="Function Operator">_∨_</a><a id="789" class="Symbol">;</a> <a id="791" href="https://agda.github.io/agda-stdlib/v0.17/Data.Bool.Base.html#730" class="Function">not</a><a id="794" class="Symbol">)</a>
<a id="796" class="Keyword">open</a> <a id="801" class="Keyword">import</a> <a id="808" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="817" class="Keyword">using</a> <a id="823" class="Symbol">(</a><a id="824" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="825" class="Symbol">;</a> <a id="827" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="831" class="Symbol">;</a> <a id="833" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="836" class="Symbol">;</a> <a id="838" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="841" class="Symbol">;</a> <a id="843" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="846" class="Symbol">;</a> <a id="848" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="851" class="Symbol">;</a> <a id="853" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="856" class="Symbol">;</a> <a id="858" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="861" class="Symbol">;</a> <a id="863" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="866" class="Symbol">)</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="900" class="Keyword">using</a>
  <a id="908" class="Symbol">(</a><a id="909" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9375" class="Function">+-assoc</a><a id="916" class="Symbol">;</a> <a id="918" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9476" class="Function">+-identityˡ</a><a id="929" class="Symbol">;</a> <a id="931" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9531" class="Function">+-identityʳ</a><a id="942" class="Symbol">;</a> <a id="944" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#15493" class="Function">*-assoc</a><a id="951" class="Symbol">;</a> <a id="953" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#14397" class="Function">*-identityˡ</a><a id="964" class="Symbol">;</a> <a id="966" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#14461" class="Function">*-identityʳ</a><a id="977" class="Symbol">)</a>
<a id="979" class="Keyword">open</a> <a id="984" class="Keyword">import</a> <a id="991" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1008" class="Keyword">using</a> <a id="1014" class="Symbol">(</a><a id="1015" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="1017" class="Symbol">;</a> <a id="1019" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#534" class="Datatype">Dec</a><a id="1022" class="Symbol">;</a> <a id="1024" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#570" class="InductiveConstructor">yes</a><a id="1027" class="Symbol">;</a> <a id="1029" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#597" class="InductiveConstructor">no</a><a id="1031" class="Symbol">)</a>
<a id="1033" class="Keyword">open</a> <a id="1038" class="Keyword">import</a> <a id="1045" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html" class="Module">Data.Product</a> <a id="1058" class="Keyword">using</a> <a id="1064" class="Symbol">(</a><a id="1065" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#1353" class="Function Operator">_×_</a><a id="1068" class="Symbol">;</a> <a id="1070" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#881" class="Function">∃</a><a id="1071" class="Symbol">;</a> <a id="1073" href="https://agda.github.io/agda-stdlib/v0.17/Data.Product.html#942" class="Function">∃-syntax</a><a id="1081" class="Symbol">)</a> <a id="1083" class="Keyword">renaming</a> <a id="1092" class="Symbol">(</a><a id="1093" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">_,_</a> <a id="1097" class="Symbol">to</a> <a id="1100" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1105" class="Symbol">)</a>
<a id="1107" class="Keyword">open</a> <a id="1112" class="Keyword">import</a> <a id="1119" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html" class="Module">Data.Empty</a> <a id="1130" class="Keyword">using</a> <a id="1136" class="Symbol">(</a><a id="1137" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#243" class="Datatype">⊥</a><a id="1138" class="Symbol">;</a> <a id="1140" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#360" class="Function">⊥-elim</a><a id="1146" class="Symbol">)</a>
<a id="1148" class="Keyword">open</a> <a id="1153" class="Keyword">import</a> <a id="1160" href="https://agda.github.io/agda-stdlib/v0.17/Function.html" class="Module">Function</a> <a id="1169" class="Keyword">using</a> <a id="1175" class="Symbol">(</a><a id="1176" href="https://agda.github.io/agda-stdlib/v0.17/Function.html#769" class="Function Operator">_∘_</a><a id="1179" class="Symbol">)</a>
<a id="1181" class="Keyword">open</a> <a id="1186" class="Keyword">import</a> <a id="1193" href="https://agda.github.io/agda-stdlib/v0.17/Algebra.Structures.html" class="Module">Algebra.Structures</a> <a id="1212" class="Keyword">using</a> <a id="1218" class="Symbol">(</a><a id="1219" href="https://agda.github.io/agda-stdlib/v0.17/Algebra.Structures.html#1339" class="Record">IsMonoid</a><a id="1227" class="Symbol">)</a>
<a id="1229" class="Keyword">open</a> <a id="1234" class="Keyword">import</a> <a id="1241" href="https://agda.github.io/agda-stdlib/v0.17/Level.html" class="Module">Level</a> <a id="1247" class="Keyword">using</a> <a id="1253" class="Symbol">(</a><a id="1254" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Primitive.html#408" class="Postulate">Level</a><a id="1259" class="Symbol">)</a>
<a id="1261" class="Keyword">open</a> <a id="1266" class="Keyword">import</a> <a id="1273" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1288" class="Keyword">using</a> <a id="1294" class="Symbol">(</a><a id="1295" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Unary.html#3313" class="Function">Decidable</a><a id="1304" class="Symbol">)</a>
<a id="1306" class="Keyword">open</a> <a id="1311" class="Keyword">import</a> <a id="1318" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1333" class="Keyword">using</a> <a id="1339" class="Symbol">(</a><a id="1340" href="plfa.Relations.html#26612" class="Datatype Operator">_&lt;_</a><a id="1343" class="Symbol">;</a> <a id="1345" href="plfa.Relations.html#26639" class="InductiveConstructor">z&lt;s</a><a id="1348" class="Symbol">;</a> <a id="1350" href="plfa.Relations.html#26696" class="InductiveConstructor">s&lt;s</a><a id="1353" class="Symbol">)</a>
<a id="1355" class="Keyword">open</a> <a id="1360" class="Keyword">import</a> <a id="1367" href="plfa.Isomorphism.html" class="Module">plfa.Isomorphism</a> <a id="1384" class="Keyword">using</a> <a id="1390" class="Symbol">(</a><a id="1391" href="plfa.Isomorphism.html#5561" class="Record Operator">_≃_</a><a id="1394" class="Symbol">;</a> <a id="1396" href="plfa.Isomorphism.html#9144" class="Function">≃-sym</a><a id="1401" class="Symbol">;</a> <a id="1403" href="plfa.Isomorphism.html#9557" class="Function">≃-trans</a><a id="1410" class="Symbol">;</a> <a id="1412" href="plfa.Isomorphism.html#11733" class="Record Operator">_≲_</a><a id="1415" class="Symbol">;</a> <a id="1417" href="plfa.Isomorphism.html#3801" class="Postulate">extensionality</a><a id="1431" class="Symbol">)</a>
<a id="1433" class="Keyword">open</a> <a id="1438" href="plfa.Isomorphism.html#10785" class="Module">plfa.Isomorphism.≃-Reasoning</a>
<a id="1467" class="Keyword">open</a> <a id="1472" class="Keyword">import</a> <a id="1479" href="plfa.Lists.html" class="Module">plfa.Lists</a> <a id="1490" class="Keyword">using</a> <a id="1496" class="Symbol">(</a><a id="1497" href="plfa.Lists.html#1325" class="Datatype">List</a><a id="1501" class="Symbol">;</a> <a id="1503" href="plfa.Lists.html#1354" class="InductiveConstructor">[]</a><a id="1505" class="Symbol">;</a> <a id="1507" href="plfa.Lists.html#1369" class="InductiveConstructor Operator">_∷_</a><a id="1510" class="Symbol">;</a> <a id="1512" href="plfa.Lists.html#3921" class="Operator">[_]</a><a id="1515" class="Symbol">;</a> <a id="1517" href="plfa.Lists.html#3944" class="Operator">[_,_]</a><a id="1522" class="Symbol">;</a> <a id="1524" href="plfa.Lists.html#3975" class="Operator">[_,_,_]</a><a id="1531" class="Symbol">;</a> <a id="1533" href="plfa.Lists.html#4014" class="Operator">[_,_,_,_]</a><a id="1542" class="Symbol">;</a>
  <a id="1546" href="plfa.Lists.html#4769" class="Function Operator">_++_</a><a id="1550" class="Symbol">;</a> <a id="1552" href="plfa.Lists.html#11165" class="Function">reverse</a><a id="1559" class="Symbol">;</a> <a id="1561" href="plfa.Lists.html#17306" class="Function">map</a><a id="1564" class="Symbol">;</a> <a id="1566" href="plfa.Lists.html#20673" class="Function">foldr</a><a id="1571" class="Symbol">;</a> <a id="1573" href="plfa.Lists.html#21813" class="Function">sum</a><a id="1576" class="Symbol">;</a> <a id="1578" href="plfa.Lists.html#28450" class="Datatype">All</a><a id="1581" class="Symbol">;</a> <a id="1583" href="plfa.Lists.html#30624" class="Datatype">Any</a><a id="1586" class="Symbol">;</a> <a id="1588" href="plfa.Lists.html#30675" class="InductiveConstructor">here</a><a id="1592" class="Symbol">;</a> <a id="1594" href="plfa.Lists.html#30732" class="InductiveConstructor">there</a><a id="1599" class="Symbol">;</a> <a id="1601" href="plfa.Lists.html#31153" class="Function Operator">_∈_</a><a id="1604" class="Symbol">)</a>
<a id="1606" class="Keyword">open</a> <a id="1611" class="Keyword">import</a> <a id="1618" href="plfa.Lambda.html" class="Module">plfa.Lambda</a> <a id="1630" class="Keyword">hiding</a> <a id="1637" class="Symbol">(</a><a id="1638" href="plfa.Lambda.html#7380" class="Function Operator">ƛ′_⇒_</a><a id="1643" class="Symbol">;</a> <a id="1645" href="plfa.Lambda.html#7501" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a><a id="1666" class="Symbol">;</a> <a id="1668" href="plfa.Lambda.html#7715" class="Function Operator">μ′_⇒_</a><a id="1673" class="Symbol">;</a> <a id="1675" href="plfa.Lambda.html#7915" class="Function">plus′</a><a id="1680" class="Symbol">)</a>
<a id="1682" class="Keyword">open</a> <a id="1687" class="Keyword">import</a> <a id="1694" href="plfa.Properties.html" class="Module">plfa.Properties</a> <a id="1710" class="Keyword">hiding</a> <a id="1717" class="Symbol">(</a><a id="1718" href="plfa.Properties.html#11951" class="Postulate">value?</a><a id="1724" class="Symbol">;</a> <a id="1726" href="plfa.Properties.html#42118" class="Postulate">unstuck</a><a id="1733" class="Symbol">;</a> <a id="1735" href="plfa.Properties.html#42334" class="Postulate">preserves</a><a id="1744" class="Symbol">;</a> <a id="1746" href="plfa.Properties.html#42587" class="Postulate">wttdgs</a><a id="1752" class="Symbol">)</a>{% endraw %}</pre>

## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
<pre class="Agda">{% raw %}<a id="ƛ′_⇒_"></a><a id="2041" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">ƛ′_⇒_</a> <a id="2047" class="Symbol">:</a> <a id="2049" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2054" class="Symbol">→</a> <a id="2056" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2061" class="Symbol">→</a> <a id="2063" href="plfa.Lambda.html#3845" class="Datatype">Term</a>
<a id="2068" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">ƛ′</a> <a id="2071" class="Symbol">(</a><a id="2072" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2074" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2074" class="Bound">x</a><a id="2075" class="Symbol">)</a> <a id="2077" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">⇒</a> <a id="2079" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2079" class="Bound">N</a>  <a id="2082" class="Symbol">=</a>  <a id="2085" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">ƛ</a> <a id="2087" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2074" class="Bound">x</a> <a id="2089" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">⇒</a> <a id="2091" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2079" class="Bound">N</a>
<a id="2093" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="CatchallClause Function Operator">ƛ′</a><a id="2095" class="CatchallClause"> </a><a id="2096" class="CatchallClause Symbol">_</a><a id="2097" class="CatchallClause"> </a><a id="2098" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="CatchallClause Function Operator">⇒</a><a id="2099" class="CatchallClause"> </a><a id="2100" class="CatchallClause Symbol">_</a>      <a id="2107" class="Symbol">=</a>  <a id="2110" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#360" class="Function">⊥-elim</a> <a id="2117" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2146" class="Postulate">impossible</a>
  <a id="2130" class="Keyword">where</a> <a id="2136" class="Keyword">postulate</a> <a id="2146" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2146" class="Postulate">impossible</a> <a id="2157" class="Symbol">:</a> <a id="2159" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#243" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="2162" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="2184" class="Symbol">:</a> <a id="2186" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2191" class="Symbol">→</a> <a id="2193" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2198" class="Symbol">→</a> <a id="2200" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2205" class="Symbol">→</a> <a id="2207" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2212" class="Symbol">→</a> <a id="2214" href="plfa.Lambda.html#3845" class="Datatype">Term</a>
<a id="2219" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">case′</a> <a id="2225" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2225" class="Bound">L</a> <a id="2227" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">[zero⇒</a> <a id="2234" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2234" class="Bound">M</a> <a id="2236" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">|suc</a> <a id="2241" class="Symbol">(</a><a id="2242" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2244" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2244" class="Bound">x</a><a id="2245" class="Symbol">)</a> <a id="2247" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">⇒</a> <a id="2249" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2249" class="Bound">N</a> <a id="2251" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">]</a>  <a id="2254" class="Symbol">=</a>  <a id="2257" href="plfa.Lambda.html#4072" class="InductiveConstructor Operator">case</a> <a id="2262" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2225" class="Bound">L</a> <a id="2264" href="plfa.Lambda.html#4072" class="InductiveConstructor Operator">[zero⇒</a> <a id="2271" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2234" class="Bound">M</a> <a id="2273" href="plfa.Lambda.html#4072" class="InductiveConstructor Operator">|suc</a> <a id="2278" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2244" class="Bound">x</a> <a id="2280" href="plfa.Lambda.html#4072" class="InductiveConstructor Operator">⇒</a> <a id="2282" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2249" class="Bound">N</a> <a id="2284" href="plfa.Lambda.html#4072" class="InductiveConstructor Operator">]</a>
<a id="2286" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="CatchallClause Function Operator">case′</a><a id="2291" class="CatchallClause"> </a><a id="2292" class="CatchallClause Symbol">_</a><a id="2293" class="CatchallClause"> </a><a id="2294" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="CatchallClause Function Operator">[zero⇒</a><a id="2300" class="CatchallClause"> </a><a id="2301" class="CatchallClause Symbol">_</a><a id="2302" class="CatchallClause"> </a><a id="2303" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="CatchallClause Function Operator">|suc</a><a id="2307" class="CatchallClause"> </a><a id="2308" class="CatchallClause Symbol">_</a><a id="2309" class="CatchallClause"> </a><a id="2310" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="CatchallClause Function Operator">⇒</a><a id="2311" class="CatchallClause"> </a><a id="2312" class="CatchallClause Symbol">_</a><a id="2313" class="CatchallClause"> </a><a id="2314" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="CatchallClause Function Operator">]</a>      <a id="2321" class="Symbol">=</a>  <a id="2324" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#360" class="Function">⊥-elim</a> <a id="2331" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2360" class="Postulate">impossible</a>
  <a id="2344" class="Keyword">where</a> <a id="2350" class="Keyword">postulate</a> <a id="2360" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2360" class="Postulate">impossible</a> <a id="2371" class="Symbol">:</a> <a id="2373" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#243" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="2376" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="Function Operator">μ′_⇒_</a> <a id="2382" class="Symbol">:</a> <a id="2384" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2389" class="Symbol">→</a> <a id="2391" href="plfa.Lambda.html#3845" class="Datatype">Term</a> <a id="2396" class="Symbol">→</a> <a id="2398" href="plfa.Lambda.html#3845" class="Datatype">Term</a>
<a id="2403" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="Function Operator">μ′</a> <a id="2406" class="Symbol">(</a><a id="2407" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2409" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2409" class="Bound">x</a><a id="2410" class="Symbol">)</a> <a id="2412" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="Function Operator">⇒</a> <a id="2414" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2414" class="Bound">N</a>  <a id="2417" class="Symbol">=</a>  <a id="2420" href="plfa.Lambda.html#4132" class="InductiveConstructor Operator">μ</a> <a id="2422" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2409" class="Bound">x</a> <a id="2424" href="plfa.Lambda.html#4132" class="InductiveConstructor Operator">⇒</a> <a id="2426" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2414" class="Bound">N</a>
<a id="2428" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="CatchallClause Function Operator">μ′</a><a id="2430" class="CatchallClause"> </a><a id="2431" class="CatchallClause Symbol">_</a><a id="2432" class="CatchallClause"> </a><a id="2433" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="CatchallClause Function Operator">⇒</a><a id="2434" class="CatchallClause"> </a><a id="2435" class="CatchallClause Symbol">_</a>      <a id="2442" class="Symbol">=</a>  <a id="2445" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#360" class="Function">⊥-elim</a> <a id="2452" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2481" class="Postulate">impossible</a>
  <a id="2465" class="Keyword">where</a> <a id="2471" class="Keyword">postulate</a> <a id="2481" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2481" class="Postulate">impossible</a> <a id="2492" class="Symbol">:</a> <a id="2494" href="https://agda.github.io/agda-stdlib/v0.17/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
The definition of `plus` can now be written as follows.
<pre class="Agda">{% raw %}<a id="plus′"></a><a id="2576" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2576" class="Function">plus′</a> <a id="2582" class="Symbol">:</a> <a id="2584" href="plfa.Lambda.html#3845" class="Datatype">Term</a>
<a id="2589" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2576" class="Function">plus′</a> <a id="2595" class="Symbol">=</a> <a id="2597" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="Function Operator">μ′</a> <a id="2600" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2707" class="Function">+</a> <a id="2602" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2376" class="Function Operator">⇒</a> <a id="2604" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">ƛ′</a> <a id="2607" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2721" class="Function">m</a> <a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">⇒</a> <a id="2611" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">ƛ′</a> <a id="2614" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2735" class="Function">n</a> <a id="2616" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2041" class="Function Operator">⇒</a>
          <a id="2628" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">case′</a> <a id="2634" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2721" class="Function">m</a>
            <a id="2648" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">[zero⇒</a> <a id="2655" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2735" class="Function">n</a>
            <a id="2669" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">|suc</a> <a id="2674" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2721" class="Function">m</a> <a id="2676" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">⇒</a> <a id="2678" href="plfa.Lambda.html#4031" class="InductiveConstructor Operator">`suc</a> <a id="2683" class="Symbol">(</a><a id="2684" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2707" class="Function">+</a> <a id="2686" href="plfa.Lambda.html#3949" class="InductiveConstructor Operator">·</a> <a id="2688" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2721" class="Function">m</a> <a id="2690" href="plfa.Lambda.html#3949" class="InductiveConstructor Operator">·</a> <a id="2692" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2735" class="Function">n</a><a id="2693" class="Symbol">)</a> <a id="2695" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2162" class="Function Operator">]</a>
  <a id="2699" class="Keyword">where</a>
  <a id="2707" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2707" class="Function">+</a>  <a id="2710" class="Symbol">=</a>  <a id="2713" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2715" class="String">&quot;+&quot;</a>
  <a id="2721" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2721" class="Function">m</a>  <a id="2724" class="Symbol">=</a>  <a id="2727" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2729" class="String">&quot;m&quot;</a>
  <a id="2735" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#2735" class="Function">n</a>  <a id="2738" class="Symbol">=</a>  <a id="2741" href="plfa.Lambda.html#3864" class="InductiveConstructor Operator">`</a> <a id="2743" class="String">&quot;n&quot;</a>{% endraw %}</pre>
Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.


#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.


#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
<pre class="Agda">{% raw %}<a id="3902" class="Keyword">postulate</a>
  <a id="value?"></a><a id="3914" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3914" class="Postulate">value?</a> <a id="3921" class="Symbol">:</a> <a id="3923" class="Symbol">∀</a> <a id="3925" class="Symbol">{</a><a id="3926" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3926" class="Bound">A</a> <a id="3928" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3928" class="Bound">M</a><a id="3929" class="Symbol">}</a> <a id="3931" class="Symbol">→</a> <a id="3933" href="plfa.Lambda.html#30865" class="InductiveConstructor">∅</a> <a id="3935" href="plfa.Lambda.html#33276" class="Datatype Operator">⊢</a> <a id="3937" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3928" class="Bound">M</a> <a id="3939" href="plfa.Lambda.html#33276" class="Datatype Operator">⦂</a> <a id="3941" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3926" class="Bound">A</a> <a id="3943" class="Symbol">→</a> <a id="3945" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Nullary.html#534" class="Datatype">Dec</a> <a id="3949" class="Symbol">(</a><a id="3950" href="plfa.Lambda.html#11634" class="Datatype">Value</a> <a id="3956" href="{% endraw %}{{ site.baseurl }}{% link out/PUC-Assignment3.md %}{% raw %}#3928" class="Bound">M</a><a id="3957" class="Symbol">)</a>{% endraw %}</pre>


#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.


#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.


#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.








