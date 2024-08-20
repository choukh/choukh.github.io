---
title: 形式化大数数学 (0.0 - 高德纳箭头, 康威链箭)
zhihu-tags: Agda, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/708256897
---

# 形式化大数数学 (0.0 - 高德纳箭头, 康威链箭)

> 交流Q群: 893531731  
> 本文源码: [Lower.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Lower.lagda.md)  
> 高亮渲染: [Lower.html](https://choukh.github.io/agda-googology/Lower.html)  

<pre class="Agda"><a id="351" class="Symbol">{-#</a> <a id="355" class="Keyword">OPTIONS</a> <a id="363" class="Pragma">--safe</a> <a id="370" class="Symbol">#-}</a>
<a id="374" class="Keyword">module</a> <a id="381" href="Lower.html" class="Module">Lower</a> <a id="387" class="Keyword">where</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="443" class="Keyword">using</a> <a id="449" class="Symbol">(</a><a id="450" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="453" class="Symbol">;</a> <a id="455" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="459" class="Symbol">)</a>
</pre>
本篇是[形式化大数数学 (1.0 - 序数, 增长层级, 不动点)](https://zhuanlan.zhihu.com/p/705306447)的前传, 我们快速介绍一些比较弱的著名大数记号, 这部分是入门的入门. 首先要理解的是各种大数记号的核心思想——迭代.

## 迭代

我们知道自然数类型 $ℕ$ 由如下两条规则定义.

$$
\frac{}{\kern{0.17em}\text{zero} : ℕ\kern{0.17em}}
\qquad
\frac{\alpha:ℕ}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:ℕ\kern{0.17em}}
$$

<pre class="Agda"><a id="782" class="Keyword">open</a> <a id="787" class="Keyword">import</a> <a id="794" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="803" class="Keyword">using</a> <a id="809" class="Symbol">(</a><a id="810" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="811" class="Symbol">;</a> <a id="813" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="817" class="Symbol">;</a> <a id="819" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="822" class="Symbol">)</a>
</pre>
**约定** 我们用 $A$ 表示任意类型.

<pre class="Agda"><a id="861" class="Keyword">private</a> <a id="869" class="Keyword">variable</a> <a id="878" href="Lower.html#878" class="Generalizable">A</a> <a id="880" class="Symbol">:</a> <a id="882" href="Agda.Primitive.html#388" class="Primitive">Set</a>
</pre>
**定义** 函数 $F : A → A$ 的 $n$ 次复合叫做 $F$ 的 $n$ 次迭代, 记作 $F^n$

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{n^+} &= F \circ F^n
\end{aligned}
$$

其中 $\text{id}$ 是恒等函数, 就是输入什么返回什么.

<pre class="Agda"><a id="1073" class="Keyword">open</a> <a id="1078" class="Keyword">import</a> <a id="1085" href="Function.html" class="Module">Function</a> <a id="1094" class="Keyword">public</a> <a id="1101" class="Keyword">using</a> <a id="1107" class="Symbol">(</a><a id="1108" href="Function.Base.html#704" class="Function">id</a><a id="1110" class="Symbol">;</a> <a id="1112" href="Function.Base.html#1115" class="Function Operator">_∘_</a><a id="1115" class="Symbol">)</a>

<a id="_∘ⁿ_"></a><a id="1118" href="Lower.html#1118" class="Function Operator">_∘ⁿ_</a> <a id="1123" class="Symbol">:</a> <a id="1125" class="Symbol">(</a><a id="1126" href="Lower.html#878" class="Generalizable">A</a> <a id="1128" class="Symbol">→</a> <a id="1130" href="Lower.html#878" class="Generalizable">A</a><a id="1131" class="Symbol">)</a> <a id="1133" class="Symbol">→</a> <a id="1135" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1137" class="Symbol">→</a> <a id="1139" class="Symbol">(</a><a id="1140" href="Lower.html#878" class="Generalizable">A</a> <a id="1142" class="Symbol">→</a> <a id="1144" href="Lower.html#878" class="Generalizable">A</a><a id="1145" class="Symbol">)</a>
<a id="1147" href="Lower.html#1147" class="Bound">F</a> <a id="1149" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1152" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>  <a id="1158" class="Symbol">=</a> <a id="1160" href="Function.Base.html#704" class="Function">id</a>
<a id="1163" href="Lower.html#1163" class="Bound">F</a> <a id="1165" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1168" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1172" href="Lower.html#1172" class="Bound">n</a> <a id="1174" class="Symbol">=</a> <a id="1176" href="Lower.html#1163" class="Bound">F</a> <a id="1178" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="1180" class="Symbol">(</a><a id="1181" href="Lower.html#1163" class="Bound">F</a> <a id="1183" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1186" href="Lower.html#1172" class="Bound">n</a><a id="1187" class="Symbol">)</a>
</pre>
## 自然数算术

**约定** 我们遵循类型论的习惯, 今后都会在无歧义的情况下省略函数应用的括号.

**定义** 从 $m$ 开始做 $n$ 次后继叫做自然数加法, 记作 $m+n$

$$
m + n := \text{suc}^n\kern{0.17em}m
$$

<pre class="Agda"><a id="_+_"></a><a id="1341" href="Lower.html#1341" class="Function Operator">_+_</a> <a id="1345" class="Symbol">:</a> <a id="1347" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1349" class="Symbol">→</a> <a id="1351" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1353" class="Symbol">→</a> <a id="1355" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1356" class="Symbol">;</a> <a id="1358" class="Keyword">infixl</a> <a id="1365" class="Number">6</a> <a id="1367" href="Lower.html#1341" class="Function Operator">_+_</a>
<a id="1371" href="Lower.html#1371" class="Bound">m</a> <a id="1373" href="Lower.html#1341" class="Function Operator">+</a> <a id="1375" href="Lower.html#1375" class="Bound">n</a> <a id="1377" class="Symbol">=</a> <a id="1379" class="Symbol">(</a><a id="1380" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1384" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1387" href="Lower.html#1375" class="Bound">n</a><a id="1388" class="Symbol">)</a> <a id="1390" href="Lower.html#1371" class="Bound">m</a>
</pre>
**定义** 从 $0$ 开始做 $n$ 次 $+ m$ 叫做自然数乘法, 记作 $m×n$, 简记作 $mn$

$$
m × n := (+m)^n\kern{0.17em}0
$$

<pre class="Agda"><a id="_*_"></a><a id="1500" href="Lower.html#1500" class="Function Operator">_*_</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1512" class="Symbol">→</a> <a id="1514" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1515" class="Symbol">;</a> <a id="1517" class="Keyword">infixl</a> <a id="1524" class="Number">7</a> <a id="1526" href="Lower.html#1500" class="Function Operator">_*_</a>
<a id="1530" href="Lower.html#1530" class="Bound">m</a> <a id="1532" href="Lower.html#1500" class="Function Operator">*</a> <a id="1534" href="Lower.html#1534" class="Bound">n</a> <a id="1536" class="Symbol">=</a> <a id="1538" class="Symbol">((</a><a id="1540" href="Lower.html#1341" class="Function Operator">_+</a> <a id="1543" href="Lower.html#1530" class="Bound">m</a><a id="1544" class="Symbol">)</a> <a id="1546" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1549" href="Lower.html#1534" class="Bound">n</a><a id="1550" class="Symbol">)</a> <a id="1552" class="Number">0</a>
</pre>
**定义** 从 $1$ 开始做 $n$ 次 $× m$ 叫做自然数幂运算, 也叫乘方, 记作 $m^n$

$$
m^n := (×m)^n\kern{0.17em}1
$$

<pre class="Agda"><a id="_^_"></a><a id="1657" href="Lower.html#1657" class="Function Operator">_^_</a> <a id="1661" class="Symbol">:</a> <a id="1663" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1665" class="Symbol">→</a> <a id="1667" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1669" class="Symbol">→</a> <a id="1671" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1672" class="Symbol">;</a> <a id="1674" class="Keyword">infixr</a> <a id="1681" class="Number">8</a> <a id="1683" href="Lower.html#1657" class="Function Operator">_^_</a>
<a id="1687" href="Lower.html#1687" class="Bound">m</a> <a id="1689" href="Lower.html#1657" class="Function Operator">^</a> <a id="1691" href="Lower.html#1691" class="Bound">n</a> <a id="1693" class="Symbol">=</a> <a id="1695" class="Symbol">((</a><a id="1697" href="Lower.html#1500" class="Function Operator">_*</a> <a id="1700" href="Lower.html#1687" class="Bound">m</a><a id="1701" class="Symbol">)</a> <a id="1703" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="1706" href="Lower.html#1691" class="Bound">n</a><a id="1707" class="Symbol">)</a> <a id="1709" class="Number">1</a>
</pre>
**例**

$$
2^5 = 32 \\
3^5 = 243
$$

<pre class="Agda"><a id="1760" href="Lower.html#1760" class="Function">_</a> <a id="1762" class="Symbol">:</a> <a id="1764" class="Number">2</a> <a id="1766" href="Lower.html#1657" class="Function Operator">^</a> <a id="1768" class="Number">5</a> <a id="1770" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="1772" class="Number">32</a>
<a id="1775" class="Symbol">_</a> <a id="1777" class="Symbol">=</a> <a id="1779" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="1785" href="Lower.html#1785" class="Function">_</a> <a id="1787" class="Symbol">:</a> <a id="1789" class="Number">3</a> <a id="1791" href="Lower.html#1657" class="Function Operator">^</a> <a id="1793" class="Number">5</a> <a id="1795" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="1797" class="Number">243</a>
<a id="1801" class="Symbol">_</a> <a id="1803" class="Symbol">=</a> <a id="1805" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
## 阿克曼函数

[阿克曼函数 (Ackermann function)](https://googology.fandom.com/wiki/Ackermann_function) 是最简单和最早发现的非原始递归的可计算全函数. 它有很多版本, 常见的双参数版本定义如下.

**定义** 双参数阿克曼函数 $\text{Ack}\kern{0.17em}m\kern{0.17em}n$

$$
\begin{aligned}
\text{Ack}\kern{0.17em}0 &:= \text{suc} \\
\text{Ack}\kern{0.17em}m^+\kern{0.17em}n&:= (\text{Ack}\kern{0.17em}m)^n\kern{0.17em}(\text{Ack}\kern{0.17em}m\kern{0.17em}1)
\end{aligned}
$$

<pre class="Agda"><a id="Ack"></a><a id="2227" href="Lower.html#2227" class="Function">Ack</a> <a id="2231" class="Symbol">:</a> <a id="2233" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2235" class="Symbol">→</a> <a id="2237" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2239" class="Symbol">→</a> <a id="2241" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="2243" href="Lower.html#2227" class="Function">Ack</a> <a id="2247" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="2252" class="Symbol">=</a> <a id="2254" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a>
<a id="2258" href="Lower.html#2227" class="Function">Ack</a> <a id="2262" class="Symbol">(</a><a id="2263" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="2267" href="Lower.html#2267" class="Bound">m</a><a id="2268" class="Symbol">)</a> <a id="2270" href="Lower.html#2270" class="Bound">n</a> <a id="2272" class="Symbol">=</a> <a id="2274" class="Symbol">(</a><a id="2275" href="Lower.html#2227" class="Function">Ack</a> <a id="2279" href="Lower.html#2267" class="Bound">m</a> <a id="2281" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="2284" href="Lower.html#2270" class="Bound">n</a><a id="2285" class="Symbol">)</a> <a id="2287" class="Symbol">(</a><a id="2288" href="Lower.html#2227" class="Function">Ack</a> <a id="2292" href="Lower.html#2267" class="Bound">m</a> <a id="2294" class="Number">1</a><a id="2295" class="Symbol">)</a>
</pre>
### 数值表

![阿克曼函数数值表](https://pic4.zhimg.com/80/v2-e37f9128a7d99a3e31001d403fa26001.png)

<pre class="Agda"><a id="2399" href="Lower.html#2399" class="Function">_</a> <a id="2401" class="Symbol">:</a> <a id="2403" href="Lower.html#2227" class="Function">Ack</a> <a id="2407" class="Number">0</a> <a id="2409" class="Number">4</a> <a id="2411" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2413" class="Number">5</a>
<a id="2415" class="Symbol">_</a> <a id="2417" class="Symbol">=</a> <a id="2419" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="2425" href="Lower.html#2425" class="Function">_</a> <a id="2427" class="Symbol">:</a> <a id="2429" href="Lower.html#2227" class="Function">Ack</a> <a id="2433" class="Number">1</a> <a id="2435" class="Number">4</a> <a id="2437" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2439" class="Number">6</a>
<a id="2441" class="Symbol">_</a> <a id="2443" class="Symbol">=</a> <a id="2445" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="2451" href="Lower.html#2451" class="Function">_</a> <a id="2453" class="Symbol">:</a> <a id="2455" href="Lower.html#2227" class="Function">Ack</a> <a id="2459" class="Number">2</a> <a id="2461" class="Number">4</a> <a id="2463" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2465" class="Number">11</a>
<a id="2468" class="Symbol">_</a> <a id="2470" class="Symbol">=</a> <a id="2472" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="2478" href="Lower.html#2478" class="Function">_</a> <a id="2480" class="Symbol">:</a> <a id="2482" href="Lower.html#2227" class="Function">Ack</a> <a id="2486" class="Number">3</a> <a id="2488" class="Number">4</a> <a id="2490" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2492" class="Number">125</a>
<a id="2496" class="Symbol">_</a> <a id="2498" class="Symbol">=</a> <a id="2500" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
从表中第 $n$ 列的形式可以看到 $\text{Ack}\kern{0.17em}m$ 大致具有第 $m$ 级运算的增长率. 其中的高德纳箭头 $↑$ 和康威链箭 $→$ 介绍如下.

## 高德纳箭头

[高德纳箭头 (Knuth's up-arrow notation)](https://googology.fandom.com/wiki/Arrow_notation) 是「将乘方看作乘法的迭代」这一思想的推广. 零个箭头是加法的迭代 (乘法), 一个箭头是乘法的迭代 (乘方), 两个箭头是一个箭头的迭代, 以此类推.

**定义** 高德纳箭头有三个参数, 左右两边是底数和指数, 中间是箭头的数量.

$$
\begin{aligned}
m ↑^0 n &:= mn \\
m ↑^{k^+} 0 &:= 1 \\
m ↑^{k^+} n^+ &:= (m ↑^k)^n\kern{0.17em}m
\end{aligned}
$$

<pre class="Agda"><a id="_↑⟨_⟩_"></a><a id="2945" href="Lower.html#2945" class="Function Operator">_↑⟨_⟩_</a> <a id="2952" class="Symbol">:</a> <a id="2954" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2956" class="Symbol">→</a> <a id="2958" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2960" class="Symbol">→</a> <a id="2962" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2964" class="Symbol">→</a> <a id="2966" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2967" class="Symbol">;</a> <a id="2969" class="Keyword">infixr</a> <a id="2976" class="Number">9</a> <a id="2978" href="Lower.html#2945" class="Function Operator">_↑⟨_⟩_</a>
<a id="2985" href="Lower.html#2985" class="Bound">m</a> <a id="2987" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="2990" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="2995" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="2997" href="Lower.html#2997" class="Bound">n</a> <a id="2999" class="Symbol">=</a> <a id="3001" href="Lower.html#2985" class="Bound">m</a> <a id="3003" href="Lower.html#1500" class="Function Operator">*</a> <a id="3005" href="Lower.html#2997" class="Bound">n</a>
<a id="3007" href="Lower.html#3007" class="Bound">m</a> <a id="3009" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3012" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3016" href="Lower.html#3016" class="Bound">k</a> <a id="3018" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3020" class="Number">0</a> <a id="3022" class="Symbol">=</a> <a id="3024" class="Number">1</a>
<a id="3026" href="Lower.html#3026" class="Bound">m</a> <a id="3028" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3031" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3035" href="Lower.html#3035" class="Bound">k</a> <a id="3037" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3039" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3043" href="Lower.html#3043" class="Bound">n</a> <a id="3045" class="Symbol">=</a> <a id="3047" class="Symbol">((</a><a id="3049" href="Lower.html#3026" class="Bound">m</a> <a id="3051" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3054" href="Lower.html#3035" class="Bound">k</a> <a id="3056" href="Lower.html#2945" class="Function Operator">⟩_</a><a id="3058" class="Symbol">)</a> <a id="3060" href="Lower.html#1118" class="Function Operator">∘ⁿ</a> <a id="3063" href="Lower.html#3043" class="Bound">n</a><a id="3064" class="Symbol">)</a> <a id="3066" href="Lower.html#3026" class="Bound">m</a>
</pre>
**例**

$$
\begin{aligned}
2 ↑^0 3 &= 2×3 &=& 2 + 2 + 2 \\
2 ↑^1 3 &= 2^3 &=& 2 × 2 × 2 \\
2 ↑^2 3 &= {^3}2 &=& 2 ^ {2 ^ 2} \\
2 ↑^3 3 &&=& 2 ↑^2 2 ↑^2 2
\end{aligned}
$$

<pre class="Agda"><a id="3252" href="Lower.html#3252" class="Function">_</a> <a id="3254" class="Symbol">:</a> <a id="3256" class="Number">2</a> <a id="3258" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3261" class="Number">0</a> <a id="3263" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3265" class="Number">3</a> <a id="3267" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3269" class="Number">2</a> <a id="3271" href="Lower.html#1341" class="Function Operator">+</a> <a id="3273" class="Number">2</a> <a id="3275" href="Lower.html#1341" class="Function Operator">+</a> <a id="3277" class="Number">2</a>
<a id="3279" class="Symbol">_</a> <a id="3281" class="Symbol">=</a> <a id="3283" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="3289" href="Lower.html#3289" class="Function">_</a> <a id="3291" class="Symbol">:</a> <a id="3293" class="Number">2</a> <a id="3295" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3298" class="Number">1</a> <a id="3300" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3302" class="Number">3</a> <a id="3304" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3306" class="Number">2</a> <a id="3308" href="Lower.html#1500" class="Function Operator">*</a> <a id="3310" class="Number">2</a> <a id="3312" href="Lower.html#1500" class="Function Operator">*</a> <a id="3314" class="Number">2</a>
<a id="3316" class="Symbol">_</a> <a id="3318" class="Symbol">=</a> <a id="3320" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="3326" href="Lower.html#3326" class="Function">_</a> <a id="3328" class="Symbol">:</a> <a id="3330" class="Number">2</a> <a id="3332" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3335" class="Number">2</a> <a id="3337" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3339" class="Number">3</a> <a id="3341" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3343" class="Number">2</a> <a id="3345" href="Lower.html#1657" class="Function Operator">^</a> <a id="3347" class="Number">2</a> <a id="3349" href="Lower.html#1657" class="Function Operator">^</a> <a id="3351" class="Number">2</a>
<a id="3353" class="Symbol">_</a> <a id="3355" class="Symbol">=</a> <a id="3357" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="3363" href="Lower.html#3363" class="Function">_</a> <a id="3365" class="Symbol">:</a> <a id="3367" class="Number">2</a> <a id="3369" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3372" class="Number">3</a> <a id="3374" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3376" class="Number">3</a> <a id="3378" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3380" class="Number">2</a> <a id="3382" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3385" class="Number">2</a> <a id="3387" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3389" class="Number">2</a> <a id="3391" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3394" class="Number">2</a> <a id="3396" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3398" class="Number">2</a>
<a id="3400" class="Symbol">_</a> <a id="3402" class="Symbol">=</a> <a id="3404" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
## 葛立恒数

[葛立恒数 (Graham's number)](https://googology.fandom.com/wiki/Graham%27s_number) 是一个入门级别的著名大数, 直观上是一个64层的箭头塔.

**定义** 定义辅助函数 $G : ℕ → ℕ$, 从4个箭头开始, 迭代 $3 ↑^n 3$ 作为箭头数量, 即

$$
\begin{aligned}
G\kern{0.17em}0 &:= 4 \\
G\kern{0.17em}n^+ &:= 3 ↑^n 3
\end{aligned}
$$

非形式地

$$
G\kern{0.17em}n := 3 ↑^{3 ↑^{... ↑^{3 ↑↑↑↑ 3} ...} 3} 3
$$

则葛立恒数为 $G\kern{0.17em}64$.

<pre class="Agda"><a id="3788" class="Keyword">module</a> <a id="Graham"></a><a id="3795" href="Lower.html#3795" class="Module">Graham</a> <a id="3802" class="Keyword">where</a>
  <a id="Graham.G"></a><a id="3810" href="Lower.html#3810" class="Function">G</a> <a id="3812" class="Symbol">:</a> <a id="3814" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3816" class="Symbol">→</a> <a id="3818" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
  <a id="3822" href="Lower.html#3810" class="Function">G</a> <a id="3824" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="3829" class="Symbol">=</a> <a id="3831" class="Number">4</a>
  <a id="3835" href="Lower.html#3810" class="Function">G</a> <a id="3837" class="Symbol">(</a><a id="3838" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3842" href="Lower.html#3842" class="Bound">n</a><a id="3843" class="Symbol">)</a> <a id="3845" class="Symbol">=</a> <a id="3847" class="Number">3</a> <a id="3849" href="Lower.html#2945" class="Function Operator">↑⟨</a> <a id="3852" href="Lower.html#3842" class="Bound">n</a> <a id="3854" href="Lower.html#2945" class="Function Operator">⟩</a> <a id="3856" class="Number">3</a>

  <a id="Graham.G64"></a><a id="3861" href="Lower.html#3861" class="Function">G64</a> <a id="3865" class="Symbol">:</a> <a id="3867" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
  <a id="3871" href="Lower.html#3861" class="Function">G64</a> <a id="3875" class="Symbol">=</a> <a id="3877" href="Lower.html#3810" class="Function">G</a> <a id="3879" class="Number">64</a>
</pre>
## 康威链箭

**约定** 我们用 $n,a_1,a_2,a_3,a_4,b,c$ 表示任意给定的自然数. $n^{++}$ 表示 $n$ 的两次后继, $n^{+++}$ 表示 $n$ 的三次后继.

<pre class="Agda"><a id="3999" class="Keyword">private</a> <a id="4007" class="Keyword">variable</a> <a id="4016" href="Lower.html#4016" class="Generalizable">n</a> <a id="4018" href="Lower.html#4018" class="Generalizable">a₁</a> <a id="4021" href="Lower.html#4021" class="Generalizable">a₂</a> <a id="4024" href="Lower.html#4024" class="Generalizable">a₃</a> <a id="4027" href="Lower.html#4027" class="Generalizable">a₄</a> <a id="4030" href="Lower.html#4030" class="Generalizable">b</a> <a id="4032" href="Lower.html#4032" class="Generalizable">c</a> <a id="4034" class="Symbol">:</a> <a id="4036" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4038" class="Keyword">private</a> <a id="4046" class="Keyword">pattern</a> <a id="2+"></a><a id="4054" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="4057" href="Lower.html#4070" class="Bound">n</a> <a id="4059" class="Symbol">=</a> <a id="4061" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4065" class="Symbol">(</a><a id="4066" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4070" href="Lower.html#4070" class="Bound">n</a><a id="4071" class="Symbol">)</a>
<a id="4073" class="Keyword">private</a> <a id="4081" class="Keyword">pattern</a> <a id="3+"></a><a id="4089" href="Lower.html#4089" class="InductiveConstructor">3+</a> <a id="4092" href="Lower.html#4110" class="Bound">n</a> <a id="4094" class="Symbol">=</a> <a id="4096" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4100" class="Symbol">(</a><a id="4101" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4105" class="Symbol">(</a><a id="4106" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4110" href="Lower.html#4110" class="Bound">n</a><a id="4111" class="Symbol">))</a>
</pre>
[康威链箭 (Conway chained arrow notation)](https://googology.fandom.com/wiki/Chained_arrow_notation) 是自然数的长度大于等于 $2$ 的有限序列. 由右箭头连接, 如

$$
a → b → ... → c → d
$$

但这里的右箭头无关紧要, 简洁起见我们形式化为参数个数大于等于 $2$ 的多元函数 $C_{n^{++}}$, 其中 $n$ 表示参数个数.

$$
C_{n^{++}}\kern{0.17em}a\kern{0.17em}b\kern{0.17em}...\kern{0.17em}c\kern{0.17em}d
$$

- $C_2$ 就定义为乘方
- $C_3$ 等价于 $n$ 个高德纳箭头
- $C_4$ 大致相当于高德纳箭头塔
- ...

形式地

**定义**

$$
\begin{aligned}
C_2\kern{0.17em}b\kern{0.17em}c &:= b^c \\
\end{aligned}
$$

<pre class="Agda"><a id="C₂"></a><a id="4605" href="Lower.html#4605" class="Function">C₂</a> <a id="4608" class="Symbol">:</a> <a id="4610" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4612" class="Symbol">→</a> <a id="4614" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4616" class="Symbol">→</a> <a id="4618" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4620" href="Lower.html#4605" class="Function">C₂</a> <a id="4623" class="Symbol">=</a> <a id="4625" href="Lower.html#1657" class="Function Operator">_^_</a>
</pre>
$$
\begin{aligned}
C_3\kern{0.17em}a\kern{0.17em}b^{++}\kern{0.17em}c^{++} &:= C_3\kern{0.17em}a\kern{0.17em}(C_3\kern{0.17em}a\kern{0.17em}b^{+}\kern{0.17em}c^{++})\kern{0.17em}c^{+} \\
C_3\kern{0.17em}a\kern{0.17em}b\kern{0.17em}1 &:= C_2\kern{0.17em}a\kern{0.17em}b
\end{aligned}
$$

其中第二行的 $c = 0$ 的情况不存在, 因为 $c = 1$ 时已退化为 $C_2$.

<pre class="Agda"><a id="C₃"></a><a id="4977" href="Lower.html#4977" class="Function">C₃</a> <a id="4980" class="Symbol">:</a> <a id="4982" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4984" class="Symbol">→</a> <a id="4986" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4988" class="Symbol">→</a> <a id="4990" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4992" class="Symbol">→</a> <a id="4994" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4996" href="Lower.html#4977" class="Function">C₃</a> <a id="4999" href="Lower.html#4999" class="Bound">a</a> <a id="5001" class="Symbol">(</a><a id="5002" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5005" href="Lower.html#5005" class="Bound">b</a><a id="5006" class="Symbol">)</a> <a id="5008" class="Symbol">(</a><a id="5009" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5012" href="Lower.html#5012" class="Bound">c</a><a id="5013" class="Symbol">)</a> <a id="5015" class="Symbol">=</a> <a id="5017" href="Lower.html#4977" class="Function">C₃</a> <a id="5020" href="Lower.html#4999" class="Bound">a</a> <a id="5022" class="Symbol">(</a><a id="5023" href="Lower.html#4977" class="Function">C₃</a> <a id="5026" href="Lower.html#4999" class="Bound">a</a> <a id="5028" class="Symbol">(</a><a id="5029" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5033" href="Lower.html#5005" class="Bound">b</a><a id="5034" class="Symbol">)</a> <a id="5036" class="Symbol">(</a><a id="5037" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5040" href="Lower.html#5012" class="Bound">c</a><a id="5041" class="Symbol">))</a> <a id="5044" class="Symbol">(</a><a id="5045" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5049" href="Lower.html#5012" class="Bound">c</a><a id="5050" class="Symbol">)</a>
<a id="5052" href="Lower.html#4977" class="CatchallClause Function">C₃</a><a id="5054" class="CatchallClause"> </a><a id="5055" href="Lower.html#5055" class="CatchallClause Bound">a</a><a id="5056" class="CatchallClause"> </a><a id="5057" href="Lower.html#5057" class="CatchallClause Bound">b</a><a id="5058" class="CatchallClause"> </a><a id="5059" class="CatchallClause Symbol">_</a> <a id="5061" class="Symbol">=</a> <a id="5063" href="Lower.html#4605" class="Function">C₂</a> <a id="5066" href="Lower.html#5055" class="Bound">a</a> <a id="5068" href="Lower.html#5057" class="Bound">b</a>
</pre>
$$
\begin{aligned}
C_4\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}b^{++}\kern{0.17em}c^{++} &:= C_4\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}(C_4\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}b^{+}\kern{0.17em}c^{++})\kern{0.17em}c^{+} \\
C_4\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}b\kern{0.17em}1 &:= C_3\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}b
\end{aligned}
$$

<pre class="Agda"><a id="C₄"></a><a id="5460" href="Lower.html#5460" class="Function">C₄</a> <a id="5463" class="Symbol">:</a> <a id="5465" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5467" class="Symbol">→</a> <a id="5469" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5471" class="Symbol">→</a> <a id="5473" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5475" class="Symbol">→</a> <a id="5477" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5479" class="Symbol">→</a> <a id="5481" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="5483" href="Lower.html#5460" class="Function">C₄</a> <a id="5486" href="Lower.html#5486" class="Bound">a₁</a> <a id="5489" href="Lower.html#5489" class="Bound">a₂</a> <a id="5492" class="Symbol">(</a><a id="5493" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5496" href="Lower.html#5496" class="Bound">b</a><a id="5497" class="Symbol">)</a> <a id="5499" class="Symbol">(</a><a id="5500" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5503" href="Lower.html#5503" class="Bound">c</a><a id="5504" class="Symbol">)</a> <a id="5506" class="Symbol">=</a> <a id="5508" href="Lower.html#5460" class="Function">C₄</a> <a id="5511" href="Lower.html#5486" class="Bound">a₁</a> <a id="5514" href="Lower.html#5489" class="Bound">a₂</a> <a id="5517" class="Symbol">(</a><a id="5518" href="Lower.html#5460" class="Function">C₄</a> <a id="5521" href="Lower.html#5486" class="Bound">a₁</a> <a id="5524" href="Lower.html#5489" class="Bound">a₂</a> <a id="5527" class="Symbol">(</a><a id="5528" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5532" href="Lower.html#5496" class="Bound">b</a><a id="5533" class="Symbol">)</a> <a id="5535" class="Symbol">(</a><a id="5536" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="5539" href="Lower.html#5503" class="Bound">c</a><a id="5540" class="Symbol">))</a> <a id="5543" class="Symbol">(</a><a id="5544" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5548" href="Lower.html#5503" class="Bound">c</a><a id="5549" class="Symbol">)</a>
<a id="5551" href="Lower.html#5460" class="CatchallClause Function">C₄</a><a id="5553" class="CatchallClause"> </a><a id="5554" href="Lower.html#5554" class="CatchallClause Bound">a₁</a><a id="5556" class="CatchallClause"> </a><a id="5557" href="Lower.html#5557" class="CatchallClause Bound">a₂</a><a id="5559" class="CatchallClause"> </a><a id="5560" href="Lower.html#5560" class="CatchallClause Bound">b</a><a id="5561" class="CatchallClause"> </a><a id="5562" class="CatchallClause Symbol">_</a> <a id="5564" class="Symbol">=</a> <a id="5566" href="Lower.html#4977" class="Function">C₃</a> <a id="5569" href="Lower.html#5554" class="Bound">a₁</a> <a id="5572" href="Lower.html#5557" class="Bound">a₂</a> <a id="5575" href="Lower.html#5560" class="Bound">b</a>
</pre>
$$
\begin{aligned}
C_5\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}b^{++}\kern{0.17em}c^{++} &:= C_5\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}(C_5\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}b^{+}\kern{0.17em}c^{++})\kern{0.17em}c^{+} \\
C_5\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}b\kern{0.17em}1 &:= C_4\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}b
\end{aligned}
$$

<pre class="Agda"><a id="C₅"></a><a id="6047" href="Lower.html#6047" class="Function">C₅</a> <a id="6050" class="Symbol">:</a> <a id="6052" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6054" class="Symbol">→</a> <a id="6056" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6058" class="Symbol">→</a> <a id="6060" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6062" class="Symbol">→</a> <a id="6064" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6066" class="Symbol">→</a> <a id="6068" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6070" class="Symbol">→</a> <a id="6072" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="6074" href="Lower.html#6047" class="Function">C₅</a> <a id="6077" href="Lower.html#6077" class="Bound">a₁</a> <a id="6080" href="Lower.html#6080" class="Bound">a₂</a> <a id="6083" href="Lower.html#6083" class="Bound">a₃</a> <a id="6086" class="Symbol">(</a><a id="6087" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6090" href="Lower.html#6090" class="Bound">b</a><a id="6091" class="Symbol">)</a> <a id="6093" class="Symbol">(</a><a id="6094" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6097" href="Lower.html#6097" class="Bound">c</a><a id="6098" class="Symbol">)</a> <a id="6100" class="Symbol">=</a> <a id="6102" href="Lower.html#6047" class="Function">C₅</a> <a id="6105" href="Lower.html#6077" class="Bound">a₁</a> <a id="6108" href="Lower.html#6080" class="Bound">a₂</a> <a id="6111" href="Lower.html#6083" class="Bound">a₃</a> <a id="6114" class="Symbol">(</a><a id="6115" href="Lower.html#6047" class="Function">C₅</a> <a id="6118" href="Lower.html#6077" class="Bound">a₁</a> <a id="6121" href="Lower.html#6080" class="Bound">a₂</a> <a id="6124" href="Lower.html#6083" class="Bound">a₃</a> <a id="6127" class="Symbol">(</a><a id="6128" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6132" href="Lower.html#6090" class="Bound">b</a><a id="6133" class="Symbol">)</a> <a id="6135" class="Symbol">(</a><a id="6136" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6139" href="Lower.html#6097" class="Bound">c</a><a id="6140" class="Symbol">))</a> <a id="6143" class="Symbol">(</a><a id="6144" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6148" href="Lower.html#6097" class="Bound">c</a><a id="6149" class="Symbol">)</a>
<a id="6151" href="Lower.html#6047" class="CatchallClause Function">C₅</a><a id="6153" class="CatchallClause"> </a><a id="6154" href="Lower.html#6154" class="CatchallClause Bound">a₁</a><a id="6156" class="CatchallClause"> </a><a id="6157" href="Lower.html#6157" class="CatchallClause Bound">a₂</a><a id="6159" class="CatchallClause"> </a><a id="6160" href="Lower.html#6160" class="CatchallClause Bound">a₃</a><a id="6162" class="CatchallClause"> </a><a id="6163" href="Lower.html#6163" class="CatchallClause Bound">b</a><a id="6164" class="CatchallClause"> </a><a id="6165" class="CatchallClause Symbol">_</a> <a id="6167" class="Symbol">=</a> <a id="6169" href="Lower.html#5460" class="Function">C₄</a> <a id="6172" href="Lower.html#6154" class="Bound">a₁</a> <a id="6175" href="Lower.html#6157" class="Bound">a₂</a> <a id="6178" href="Lower.html#6160" class="Bound">a₃</a> <a id="6181" href="Lower.html#6163" class="Bound">b</a>
</pre>
现在我们要推广到任意 $n \ge 2$ 元. 观察 $C_2$ 到 $C_5$ 的形式, 不难发现 $C_2$, $C_3\kern{0.17em}a$, $C_4\kern{0.17em}a_1\kern{0.17em}a_2$, $C_5\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3$ 的类型都是 $ℕ → ℕ → ℕ$, 于是可以抽象出以下共通形式

$$
\begin{aligned}
C_+ &: (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ \\
C_+\kern{0.17em}C\kern{0.17em}a\kern{0.17em}b^{++}\kern{0.17em}c^{++} &:= C_+\kern{0.17em}C\kern{0.17em}a\kern{0.17em}(C_+\kern{0.17em}C\kern{0.17em}a\kern{0.17em}b^{+}\kern{0.17em}c^{++})\kern{0.17em}c^{+} \\
C_+\kern{0.17em}C\kern{0.17em}a\kern{0.17em}b\kern{0.17em}1 &:= C\kern{0.17em}a\kern{0.17em}b
\end{aligned}
$$

<pre class="Agda"><a id="C₊"></a><a id="6781" href="Lower.html#6781" class="Function">C₊</a> <a id="6784" class="Symbol">:</a> <a id="6786" class="Symbol">(</a><a id="6787" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6789" class="Symbol">→</a> <a id="6791" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6793" class="Symbol">→</a> <a id="6795" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="6796" class="Symbol">)</a> <a id="6798" class="Symbol">→</a> <a id="6800" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6802" class="Symbol">→</a> <a id="6804" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6806" class="Symbol">→</a> <a id="6808" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6810" class="Symbol">→</a> <a id="6812" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="6814" href="Lower.html#6781" class="Function">C₊</a> <a id="6817" href="Lower.html#6817" class="Bound">C</a> <a id="6819" href="Lower.html#6819" class="Bound">a</a> <a id="6821" class="Symbol">(</a><a id="6822" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6825" href="Lower.html#6825" class="Bound">b</a><a id="6826" class="Symbol">)</a> <a id="6828" class="Symbol">(</a><a id="6829" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6832" href="Lower.html#6832" class="Bound">c</a><a id="6833" class="Symbol">)</a> <a id="6835" class="Symbol">=</a> <a id="6837" href="Lower.html#6781" class="Function">C₊</a> <a id="6840" href="Lower.html#6817" class="Bound">C</a> <a id="6842" href="Lower.html#6819" class="Bound">a</a> <a id="6844" class="Symbol">(</a><a id="6845" href="Lower.html#6781" class="Function">C₊</a> <a id="6848" href="Lower.html#6817" class="Bound">C</a> <a id="6850" href="Lower.html#6819" class="Bound">a</a> <a id="6852" class="Symbol">(</a><a id="6853" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6857" href="Lower.html#6825" class="Bound">b</a><a id="6858" class="Symbol">)</a> <a id="6860" class="Symbol">(</a><a id="6861" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="6864" href="Lower.html#6832" class="Bound">c</a><a id="6865" class="Symbol">))</a> <a id="6868" class="Symbol">(</a><a id="6869" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6873" href="Lower.html#6832" class="Bound">c</a><a id="6874" class="Symbol">)</a>
<a id="6876" href="Lower.html#6781" class="CatchallClause Function">C₊</a><a id="6878" class="CatchallClause"> </a><a id="6879" href="Lower.html#6879" class="CatchallClause Bound">C</a><a id="6880" class="CatchallClause"> </a><a id="6881" href="Lower.html#6881" class="CatchallClause Bound">a</a><a id="6882" class="CatchallClause"> </a><a id="6883" href="Lower.html#6883" class="CatchallClause Bound">b</a><a id="6884" class="CatchallClause"> </a><a id="6885" class="CatchallClause Symbol">_</a> <a id="6887" class="Symbol">=</a> <a id="6889" href="Lower.html#6879" class="Bound">C</a> <a id="6891" href="Lower.html#6881" class="Bound">a</a> <a id="6893" href="Lower.html#6883" class="Bound">b</a>
</pre>
于是我们可以将 $C_3$ 到 $C_5$ 的定义换成

$$
\begin{aligned}
C_3 &:= C_+\kern{0.17em}C_2 \\
C_4\kern{0.17em}a &:= C_+\kern{0.17em}(C_3\kern{0.17em}a) \\
C_5\kern{0.17em}a_1\kern{0.17em}a_2 &:= C_+\kern{0.17em}(C_4\kern{0.17em}a_1\kern{0.17em}a_2)
\end{aligned}
$$

<pre class="Agda"><a id="C₃′"></a><a id="7160" href="Lower.html#7160" class="Function">C₃′</a> <a id="7164" class="Symbol">:</a> <a id="7166" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7168" class="Symbol">→</a> <a id="7170" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7172" class="Symbol">→</a> <a id="7174" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7176" class="Symbol">→</a> <a id="7178" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="7180" href="Lower.html#7160" class="Function">C₃′</a> <a id="7184" class="Symbol">=</a> <a id="7186" href="Lower.html#6781" class="Function">C₊</a> <a id="7189" href="Lower.html#4605" class="Function">C₂</a>

<a id="C₄′"></a><a id="7193" href="Lower.html#7193" class="Function">C₄′</a> <a id="7197" class="Symbol">:</a> <a id="7199" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7201" class="Symbol">→</a> <a id="7203" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7205" class="Symbol">→</a> <a id="7207" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7209" class="Symbol">→</a> <a id="7211" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7213" class="Symbol">→</a> <a id="7215" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="7217" href="Lower.html#7193" class="Function">C₄′</a> <a id="7221" href="Lower.html#7221" class="Bound">a</a> <a id="7223" class="Symbol">=</a> <a id="7225" href="Lower.html#6781" class="Function">C₊</a> <a id="7228" class="Symbol">(</a><a id="7229" href="Lower.html#7160" class="Function">C₃′</a> <a id="7233" href="Lower.html#7221" class="Bound">a</a><a id="7234" class="Symbol">)</a>

<a id="C₅′"></a><a id="7237" href="Lower.html#7237" class="Function">C₅′</a> <a id="7241" class="Symbol">:</a> <a id="7243" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7245" class="Symbol">→</a> <a id="7247" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7249" class="Symbol">→</a> <a id="7251" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7253" class="Symbol">→</a> <a id="7255" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7257" class="Symbol">→</a> <a id="7259" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7261" class="Symbol">→</a> <a id="7263" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="7265" href="Lower.html#7237" class="Function">C₅′</a> <a id="7269" href="Lower.html#7269" class="Bound">a₁</a> <a id="7272" href="Lower.html#7272" class="Bound">a₂</a> <a id="7275" class="Symbol">=</a> <a id="7277" href="Lower.html#6781" class="Function">C₊</a> <a id="7280" class="Symbol">(</a><a id="7281" href="Lower.html#7193" class="Function">C₄′</a> <a id="7285" href="Lower.html#7269" class="Bound">a₁</a> <a id="7288" href="Lower.html#7272" class="Bound">a₂</a><a id="7290" class="Symbol">)</a>
</pre>
但现在我们还写不出任意 $C_n$, 因为首先要写出它的类型.

**定义** 陪域为 $A$ 的有限元自然数函数 $\overbrace{ℕ→...→ℕ}^n →A$, 记作 $A^{→n}$, 递归定义为

$$
\begin{aligned}
A^{→0} &:= A \\
A^{→n^+} &:= ℕ → A^{→n}
\end{aligned}
$$

<pre class="Agda"><a id="_→ⁿ_"></a><a id="7488" href="Lower.html#7488" class="Function Operator">_→ⁿ_</a> <a id="7493" class="Symbol">:</a> <a id="7495" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="7499" class="Symbol">→</a> <a id="7501" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7503" class="Symbol">→</a> <a id="7505" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="7509" href="Lower.html#7509" class="Bound">A</a> <a id="7511" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="7514" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="7519" class="Symbol">=</a> <a id="7521" href="Lower.html#7509" class="Bound">A</a>
<a id="7523" href="Lower.html#7523" class="Bound">A</a> <a id="7525" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="7528" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="7532" href="Lower.html#7532" class="Bound">n</a> <a id="7534" class="Symbol">=</a> <a id="7536" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="7538" class="Symbol">→</a> <a id="7540" href="Lower.html#7523" class="Bound">A</a> <a id="7542" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="7545" href="Lower.html#7532" class="Bound">n</a>
</pre>
观察 $C_+$ 的类型, 为了适用它, 还需要柯里化和反柯里化前 $n$ 个参数. 我们使用自然数的 $n$ 维向量 $\vec{a}^n : \text{Vec}\kern{0.17em}ℕ\kern{0.17em}n$ 来容纳反柯里化出来的 $n$ 个参数. 我们用 $[\kern{0.17em}]$ 表示空向量, 用 $a :: \vec{a}^n$ 表示向量的头尾.

<pre class="Agda"><a id="7751" class="Keyword">open</a> <a id="7756" class="Keyword">import</a> <a id="7763" href="Data.Vec.html" class="Module">Data.Vec</a> <a id="7772" class="Keyword">using</a> <a id="7778" class="Symbol">(</a><a id="7779" href="Data.Vec.Base.html#1111" class="Datatype">Vec</a><a id="7782" class="Symbol">;</a> <a id="7784" href="Data.Vec.Base.html#1166" class="InductiveConstructor Operator">_∷_</a><a id="7787" class="Symbol">;</a> <a id="7789" href="Data.Vec.Base.html#1147" class="InductiveConstructor">[]</a><a id="7791" class="Symbol">)</a>
</pre>
**定义** 递归定义函数 $\text{uncurry}_2$ 将 $ℕ^{→n^{++}}$ 反柯里化为 $\text{Vec}\kern{0.17em}ℕ\kern{0.17em}n → ℕ → ℕ → ℕ$

$$
\begin{aligned}
\text{uncurry}_2\kern{0.17em}F\kern{0.17em}[\kern{0.17em}] &:= F \\
\text{uncurry}_2\kern{0.17em}F\kern{0.17em}(a :: \vec{a}^n) &:= \text{uncurry}_2\kern{0.17em}(F\kern{0.17em}a)\kern{0.17em}\vec{a}^n
\end{aligned}
$$

<pre class="Agda"><a id="uncurry₂"></a><a id="8153" href="Lower.html#8153" class="Function">uncurry₂</a> <a id="8162" class="Symbol">:</a> <a id="8164" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8166" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="8169" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="8172" href="Lower.html#4016" class="Generalizable">n</a> <a id="8174" class="Symbol">→</a> <a id="8176" class="Symbol">(</a><a id="8177" href="Data.Vec.Base.html#1111" class="Datatype">Vec</a> <a id="8181" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8183" href="Lower.html#4016" class="Generalizable">n</a> <a id="8185" class="Symbol">→</a> <a id="8187" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8189" class="Symbol">→</a> <a id="8191" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8193" class="Symbol">→</a> <a id="8195" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8196" class="Symbol">)</a>
<a id="8198" href="Lower.html#8153" class="Function">uncurry₂</a> <a id="8207" class="Symbol">{</a><a id="8208" class="Argument">n</a> <a id="8210" class="Symbol">=</a> <a id="8212" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="8216" class="Symbol">}</a> <a id="8218" href="Lower.html#8218" class="Bound">F</a> <a id="8220" href="Data.Vec.Base.html#1147" class="InductiveConstructor">[]</a> <a id="8223" class="Symbol">=</a> <a id="8225" href="Lower.html#8218" class="Bound">F</a>
<a id="8227" href="Lower.html#8153" class="Function">uncurry₂</a> <a id="8236" class="Symbol">{</a><a id="8237" class="Argument">n</a> <a id="8239" class="Symbol">=</a> <a id="8241" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="8245" href="Lower.html#8245" class="Bound">n</a><a id="8246" class="Symbol">}</a> <a id="8248" href="Lower.html#8248" class="Bound">F</a> <a id="8250" class="Symbol">(</a><a id="8251" href="Lower.html#8251" class="Bound">a</a> <a id="8253" href="Data.Vec.Base.html#1166" class="InductiveConstructor Operator">∷</a> <a id="8255" href="Lower.html#8255" class="Bound">a⃗</a><a id="8257" class="Symbol">)</a> <a id="8259" class="Symbol">=</a> <a id="8261" href="Lower.html#8153" class="Function">uncurry₂</a> <a id="8270" class="Symbol">(</a><a id="8271" href="Lower.html#8248" class="Bound">F</a> <a id="8273" href="Lower.html#8251" class="Bound">a</a><a id="8274" class="Symbol">)</a> <a id="8276" href="Lower.html#8255" class="Bound">a⃗</a>
</pre>
**定义** 递归定义函数 $\text{curry}_3$ 将 $\text{Vec}\kern{0.17em}ℕ\kern{0.17em}n → ℕ → ℕ → ℕ → ℕ$ 柯里化为 $ℕ^{→n^{+++}}$

$$
\begin{aligned}
\text{curry}_3\kern{0.17em}F &:= F\kern{0.17em}[\kern{0.17em}] \\
\text{curry}_3\kern{0.17em}F\kern{0.17em}a &:= \text{curry}_3\kern{0.17em}λ \vec{a}^n , F\kern{0.17em}(a :: \vec{a}^n)
\end{aligned}
$$

<pre class="Agda"><a id="curry₃"></a><a id="8625" href="Lower.html#8625" class="Function">curry₃</a> <a id="8632" class="Symbol">:</a> <a id="8634" class="Symbol">(</a><a id="8635" href="Data.Vec.Base.html#1111" class="Datatype">Vec</a> <a id="8639" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8641" href="Lower.html#4016" class="Generalizable">n</a> <a id="8643" class="Symbol">→</a> <a id="8645" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8647" class="Symbol">→</a> <a id="8649" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8651" class="Symbol">→</a> <a id="8653" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8655" class="Symbol">→</a> <a id="8657" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8658" class="Symbol">)</a> <a id="8660" class="Symbol">→</a> <a id="8662" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8664" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="8667" href="Lower.html#4089" class="InductiveConstructor">3+</a> <a id="8670" href="Lower.html#4016" class="Generalizable">n</a>
<a id="8672" href="Lower.html#8625" class="Function">curry₃</a> <a id="8679" class="Symbol">{</a><a id="8680" class="Argument">n</a> <a id="8682" class="Symbol">=</a> <a id="8684" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="8688" class="Symbol">}</a> <a id="8690" href="Lower.html#8690" class="Bound">F</a> <a id="8692" class="Symbol">=</a> <a id="8694" href="Lower.html#8690" class="Bound">F</a> <a id="8696" href="Data.Vec.Base.html#1147" class="InductiveConstructor">[]</a>
<a id="8699" href="Lower.html#8625" class="Function">curry₃</a> <a id="8706" class="Symbol">{</a><a id="8707" class="Argument">n</a> <a id="8709" class="Symbol">=</a> <a id="8711" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="8715" href="Lower.html#8715" class="Bound">n</a><a id="8716" class="Symbol">}</a> <a id="8718" href="Lower.html#8718" class="Bound">F</a> <a id="8720" href="Lower.html#8720" class="Bound">a</a> <a id="8722" class="Symbol">=</a> <a id="8724" href="Lower.html#8625" class="Function">curry₃</a> <a id="8731" class="Symbol">λ</a> <a id="8733" href="Lower.html#8733" class="Bound">a⃗</a> <a id="8736" class="Symbol">→</a> <a id="8738" href="Lower.html#8718" class="Bound">F</a> <a id="8740" class="Symbol">(</a><a id="8741" href="Lower.html#8720" class="Bound">a</a> <a id="8743" href="Data.Vec.Base.html#1166" class="InductiveConstructor Operator">∷</a> <a id="8745" href="Lower.html#8733" class="Bound">a⃗</a><a id="8747" class="Symbol">)</a>
</pre>
终于

**定义** 递归定义任意 $n \ge 2$ 元康威链箭 $C_{n^{++}} : \prod_n ℕ^{→n^{++}}$

$$
\begin{aligned}
C_2\kern{0.17em}m\kern{0.17em}n &:= m^n \\
C_{n^{+++}} &:= \text{curry}_3\kern{0.17em}λ \vec{a}^n , C_+\kern{0.17em}(\text{uncurry}_2\kern{0.17em}C_{n^{++}}\kern{0.17em}\vec{a}^n)
\end{aligned}
$$

<pre class="Agda"><a id="C₂₊ₙ"></a><a id="9049" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9054" class="Symbol">:</a> <a id="9056" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9058" href="Lower.html#7488" class="Function Operator">→ⁿ</a> <a id="9061" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="9064" href="Lower.html#4016" class="Generalizable">n</a>
<a id="9066" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9071" class="Symbol">{</a><a id="9072" class="Argument">n</a> <a id="9074" class="Symbol">=</a> <a id="9076" class="Number">0</a><a id="9077" class="Symbol">}</a> <a id="9079" class="Symbol">=</a> <a id="9081" href="Lower.html#1657" class="Function Operator">_^_</a>
<a id="9085" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9090" class="Symbol">{</a><a id="9091" class="Argument">n</a> <a id="9093" class="Symbol">=</a> <a id="9095" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="9099" href="Lower.html#9099" class="Bound">n</a><a id="9100" class="Symbol">}</a> <a id="9102" class="Symbol">=</a> <a id="9104" href="Lower.html#8625" class="Function">curry₃</a> <a id="9111" class="Symbol">λ</a> <a id="9113" href="Lower.html#9113" class="Bound">a⃗</a> <a id="9116" class="Symbol">→</a> <a id="9118" href="Lower.html#6781" class="Function">C₊</a> <a id="9121" class="Symbol">(</a><a id="9122" href="Lower.html#8153" class="Function">uncurry₂</a> <a id="9131" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9136" href="Lower.html#9113" class="Bound">a⃗</a><a id="9138" class="Symbol">)</a>
</pre>
**注意** 我们的这个定义并非最简, 而是综合考虑了

- 能循序渐进地理解定义
- 能通过 Agda 的自动停机检查

**事实** 不难验证

$$
\begin{aligned}
C_2\kern{0.17em}b\kern{0.17em}c &= b ^ c \\
C_3\kern{0.17em}2\kern{0.17em}2\kern{0.17em}1 &= C_2\kern{0.17em}2\kern{0.17em}2 \\
C_4\kern{0.17em}2\kern{0.17em}2\kern{0.17em}1\kern{0.17em}9 &= C_2\kern{0.17em}2\kern{0.17em}2 \\
C_5\kern{0.17em}2\kern{0.17em}2\kern{0.17em}2\kern{0.17em}1\kern{0.17em}9 &= C_3\kern{0.17em}2\kern{0.17em}2\kern{0.17em}2 \\
C_6\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}a_4\kern{0.17em}b^{++}\kern{0.17em}c^{++} &= C_6\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}a_4\kern{0.17em}(C_6\kern{0.17em}a_1\kern{0.17em}a_2\kern{0.17em}a_3\kern{0.17em}a_4\kern{0.17em}b^{+}\kern{0.17em}c^{++})\kern{0.17em}c^{+}
\end{aligned}
$$

<pre class="Agda"><a id="9931" href="Lower.html#9931" class="Function">_</a> <a id="9933" class="Symbol">:</a> <a id="9935" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9940" class="Symbol">{</a><a id="9941" class="Number">0</a><a id="9942" class="Symbol">}</a> <a id="9944" href="Lower.html#4030" class="Generalizable">b</a> <a id="9946" href="Lower.html#4032" class="Generalizable">c</a> <a id="9948" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9950" href="Lower.html#4030" class="Generalizable">b</a> <a id="9952" href="Lower.html#1657" class="Function Operator">^</a> <a id="9954" href="Lower.html#4032" class="Generalizable">c</a>
<a id="9956" class="Symbol">_</a> <a id="9958" class="Symbol">=</a> <a id="9960" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="9966" href="Lower.html#9966" class="Function">_</a> <a id="9968" class="Symbol">:</a> <a id="9970" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9975" class="Symbol">{</a><a id="9976" class="Number">1</a><a id="9977" class="Symbol">}</a> <a id="9979" class="Number">2</a> <a id="9981" class="Number">2</a> <a id="9983" class="Number">1</a> <a id="9985" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9987" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="9992" class="Symbol">{</a><a id="9993" class="Number">0</a><a id="9994" class="Symbol">}</a> <a id="9996" class="Number">2</a> <a id="9998" class="Number">2</a>
<a id="10000" class="Symbol">_</a> <a id="10002" class="Symbol">=</a> <a id="10004" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="10010" href="Lower.html#10010" class="Function">_</a> <a id="10012" class="Symbol">:</a> <a id="10014" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10019" class="Symbol">{</a><a id="10020" class="Number">2</a><a id="10021" class="Symbol">}</a> <a id="10023" class="Number">2</a> <a id="10025" class="Number">2</a> <a id="10027" class="Number">1</a> <a id="10029" class="Number">9</a> <a id="10031" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10033" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10038" class="Symbol">{</a><a id="10039" class="Number">0</a><a id="10040" class="Symbol">}</a> <a id="10042" class="Number">2</a> <a id="10044" class="Number">2</a>
<a id="10046" class="Symbol">_</a> <a id="10048" class="Symbol">=</a> <a id="10050" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="10056" href="Lower.html#10056" class="Function">_</a> <a id="10058" class="Symbol">:</a> <a id="10060" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10065" class="Symbol">{</a><a id="10066" class="Number">3</a><a id="10067" class="Symbol">}</a> <a id="10069" class="Number">2</a> <a id="10071" class="Number">2</a> <a id="10073" class="Number">2</a> <a id="10075" class="Number">1</a> <a id="10077" class="Number">9</a> <a id="10079" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10081" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10086" class="Symbol">{</a><a id="10087" class="Number">1</a><a id="10088" class="Symbol">}</a> <a id="10090" class="Number">2</a> <a id="10092" class="Number">2</a> <a id="10094" class="Number">2</a>
<a id="10096" class="Symbol">_</a> <a id="10098" class="Symbol">=</a> <a id="10100" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="10106" href="Lower.html#10106" class="Function">_</a> <a id="10108" class="Symbol">:</a> <a id="10110" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10115" class="Symbol">{</a><a id="10116" class="Number">4</a><a id="10117" class="Symbol">}</a> <a id="10119" href="Lower.html#4018" class="Generalizable">a₁</a> <a id="10122" href="Lower.html#4021" class="Generalizable">a₂</a> <a id="10125" href="Lower.html#4024" class="Generalizable">a₃</a> <a id="10128" href="Lower.html#4027" class="Generalizable">a₄</a> <a id="10131" class="Symbol">(</a><a id="10132" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="10135" href="Lower.html#4030" class="Generalizable">b</a><a id="10136" class="Symbol">)</a> <a id="10138" class="Symbol">(</a><a id="10139" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="10142" href="Lower.html#4032" class="Generalizable">c</a><a id="10143" class="Symbol">)</a> <a id="10145" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10147" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10152" class="Symbol">{</a><a id="10153" class="Number">4</a><a id="10154" class="Symbol">}</a> <a id="10156" href="Lower.html#4018" class="Generalizable">a₁</a> <a id="10159" href="Lower.html#4021" class="Generalizable">a₂</a> <a id="10162" href="Lower.html#4024" class="Generalizable">a₃</a> <a id="10165" href="Lower.html#4027" class="Generalizable">a₄</a> <a id="10168" class="Symbol">(</a><a id="10169" href="Lower.html#9049" class="Function">C₂₊ₙ</a> <a id="10174" class="Symbol">{</a><a id="10175" class="Number">4</a><a id="10176" class="Symbol">}</a> <a id="10178" href="Lower.html#4018" class="Generalizable">a₁</a> <a id="10181" href="Lower.html#4021" class="Generalizable">a₂</a> <a id="10184" href="Lower.html#4024" class="Generalizable">a₃</a> <a id="10187" href="Lower.html#4027" class="Generalizable">a₄</a> <a id="10190" class="Symbol">(</a><a id="10191" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="10195" href="Lower.html#4030" class="Generalizable">b</a><a id="10196" class="Symbol">)</a> <a id="10198" class="Symbol">(</a><a id="10199" href="Lower.html#4054" class="InductiveConstructor">2+</a> <a id="10202" href="Lower.html#4032" class="Generalizable">c</a><a id="10203" class="Symbol">))</a> <a id="10206" class="Symbol">(</a><a id="10207" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="10211" href="Lower.html#4032" class="Generalizable">c</a><a id="10212" class="Symbol">)</a>
<a id="10214" class="Symbol">_</a> <a id="10216" class="Symbol">=</a> <a id="10218" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
更高增长率的函数请看正篇 [形式化大数数学 (1.0 - 序数, 增长层级, 不动点)](https://zhuanlan.zhihu.com/p/705306447), 那里的起点就远大于以上定义的所有函数.
