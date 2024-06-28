---
title: 形式化大数数学 (1.1 - 序数, FGH, 不动点)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/705306447
---

# 形式化大数数学 (1.1 - 序数, FGH, 不动点)

> 交流Q群: 893531731  
> 本文源码: [Basic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Basic.lagda.md)  
> 高亮渲染: [Basic.html](https://choukh.github.io/agda-googology/Veblen.Basic.html)  

## 前言

本系列文章是可运行且保证停机的[大数](https://zh.wikipedia.org/wiki/%E5%A4%A7%E6%95%B0_(%E6%95%B0%E5%AD%A6))计算程序的[文学编程 (literate programming)](https://zh.wikipedia.org/wiki/%E6%96%87%E5%AD%A6%E7%BC%96%E7%A8%8B) 实现.

- **可运行**是相对于自然语言的数学描述而言, 本文贴出的代码可以在电脑上运行.
- **保证停机**是相对于[图灵完备 (Turing-complete)](https://zh.wikipedia.org/wiki/%E5%9C%96%E9%9D%88%E5%AE%8C%E5%82%99%E6%80%A7) 语言 (如C语言) 而言, 本文使用的 [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)) 语言并非图灵完备, 其自带[停机检查 (termination checking)](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/termination-checking.html), 写出的程序保证停机.
- **文学编程**是指本文既是程序代码, 也是程序文档, 代码和文档交织在一起, 以增强可读性.
  - Agda 程序会自动抽取本文所有代码块中的代码, 并执行类型检查, 而忽略代码块以外的内容.
  - ※ 冷知识: 文学编程的发明者[高德纳 (Donald Knuth)](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%BA%B3), 也是大数数学入门级内容[高德纳箭号](https://zh.wikipedia.org/wiki/%E9%AB%98%E5%BE%B7%E7%B4%8D%E7%AE%AD%E8%99%9F%E8%A1%A8%E7%A4%BA%E6%B3%95)的发明者, 也是排版软件 [TeX](https://zh.wikipedia.org/wiki/TeX) 的发明者.

也就是说, 提供足够的时间, 能量和内存, 本文介绍的大数计算程序可以真正算出一个大数. 如果真的想运行:
1. 参考 [Installation](https://agda.readthedocs.io/en/latest/getting-started/installation.html) 安装 Agda.
2. 进本文所在Github仓库 ([agda-googology](https://github.com/choukh/agda-googology)) 下载本文 markdown 源码.
3. 用编辑器打开源码, 确认进入了 [agda-mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html), 键入 `C-c C-n` 对本文定义的任意大数 (如文末的 `oom`) 执行正规化 (normalization).

### 目标人群

- 大数数学已入门 (如, 看完[大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)), 对严格性和精确定义有进一步要求的读者.
- Agda 已入门 (如, 看完 [PLFA](https://agda-zh.github.io/PLFA-zh/)), 对大数计算程序的编程实现感兴趣的读者.

只对前者感兴趣的读者, 可以忽略代码部分, 而只阅读文学部分, 它们可以看作是基于朴素类型论的数学描述, 并使用了 $\LaTeX$ 公式, 以对齐通常的数学习惯.

### 补充材料

- [core.exe - 大数数学入门](https://www.zhihu.com/column/c_1307845959598960640)
- [core.exe - 大数数学入门 - 重置版](https://www.zhihu.com/column/c_1697290814588301312)
- [oCaU - Agda大序数](https://zhuanlan.zhihu.com/p/572691308)
  - 该文详细讨论了上至二元Veblen层级的序性质, 而本文不会讨论这些性质.
- [oCaU - LVO 的 Coq 实现](https://github.com/choukh/Googology)
  - 纯代码, 无文学

### 标准库依赖

<pre class="Agda"><a id="2374" class="Keyword">module</a> <a id="2381" href="Veblen.Basic.html" class="Module">Veblen.Basic</a> <a id="2394" class="Keyword">where</a>

<a id="2401" class="Keyword">open</a> <a id="2406" class="Keyword">import</a> <a id="2413" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="2422" class="Keyword">public</a> <a id="2429" class="Keyword">using</a> <a id="2435" class="Symbol">(</a><a id="2436" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2437" class="Symbol">;</a> <a id="2439" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="2443" class="Symbol">;</a> <a id="2445" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="2448" class="Symbol">;</a> <a id="2450" href="Data.Nat.Base.html#1095" class="InductiveConstructor">2+</a><a id="2452" class="Symbol">)</a>
<a id="2454" class="Keyword">open</a> <a id="2459" class="Keyword">import</a> <a id="2466" href="Data.Unit.html" class="Module">Data.Unit</a> <a id="2476" class="Keyword">public</a> <a id="2483" class="Keyword">using</a> <a id="2489" class="Symbol">(</a><a id="2490" href="Agda.Builtin.Unit.html#175" class="Record">⊤</a><a id="2491" class="Symbol">;</a> <a id="2493" href="Agda.Builtin.Unit.html#212" class="InductiveConstructor">tt</a><a id="2495" class="Symbol">)</a>
<a id="2497" class="Keyword">open</a> <a id="2502" class="Keyword">import</a> <a id="2509" href="Function.html" class="Module">Function</a> <a id="2518" class="Keyword">public</a> <a id="2525" class="Keyword">using</a> <a id="2531" class="Symbol">(</a><a id="2532" href="Function.Base.html#704" class="Function">id</a><a id="2534" class="Symbol">;</a> <a id="2536" href="Function.Base.html#1115" class="Function Operator">_∘_</a><a id="2539" class="Symbol">;</a> <a id="2541" href="Function.Base.html#1974" class="Function Operator">_$_</a><a id="2544" class="Symbol">;</a> <a id="2546" href="Function.Base.html#4486" class="Function Operator">_∋_</a><a id="2549" class="Symbol">)</a>
<a id="2551" class="Keyword">open</a> <a id="2556" class="Keyword">import</a> <a id="2563" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2601" class="Symbol">as</a> <a id="2604" class="Module">Eq</a> <a id="2607" class="Keyword">public</a>
  <a id="2616" class="Keyword">using</a> <a id="2622" class="Symbol">(</a><a id="2623" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="2626" class="Symbol">;</a> <a id="2628" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="2632" class="Symbol">;</a> <a id="2634" href="Relation.Binary.PropositionalEquality.Core.html#1158" class="Function">cong</a><a id="2638" class="Symbol">;</a> <a id="2640" href="Relation.Binary.PropositionalEquality.Core.html#1489" class="Function">cong-app</a><a id="2648" class="Symbol">)</a>
<a id="2650" class="Keyword">open</a> <a id="2655" href="Relation.Binary.PropositionalEquality.Properties.html#6744" class="Module">Eq.≡-Reasoning</a> <a id="2670" class="Keyword">public</a>
</pre>
## 序数的定义

我们知道自然数类型 $ℕ$ 由如下两条规则定义.

$$
\frac{}{\kern{0.17em}\text{zero} : ℕ\kern{0.17em}}
\qquad
\frac{\alpha:ℕ}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:ℕ\kern{0.17em}}
$$

**定义** 我们的序数类型 $\text{Ord}$ 在 $ℕ$ 的基础上增加了第三条规则 $\text{lim}$, 即如果 $f$ 是 $ℕ$ 到序数的函数, 那么 $\text{lim}\kern{0.17em}f$ 也是序数.

$$
\frac{}{\kern{0.17em}\text{zero} : \text{Ord}\kern{0.17em}}
\qquad
\frac{\alpha:\text{Ord}}{\kern{0.17em}\text{suc}\kern{0.17em}\alpha:\text{Ord}\kern{0.17em}}
\qquad
\frac{\kern{0.17em}f : ℕ\rightarrow\text{Ord}\kern{0.17em}}{\text{lim}\kern{0.17em}f:\text{Ord}}
$$

<pre class="Agda"><a id="3257" class="Keyword">data</a> <a id="Ord"></a><a id="3262" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="3266" class="Symbol">:</a> <a id="3268" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3272" class="Keyword">where</a>
  <a id="Ord.zero"></a><a id="3280" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a> <a id="3285" class="Symbol">:</a> <a id="3287" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="Ord.suc"></a><a id="3293" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a>  <a id="3298" class="Symbol">:</a> <a id="3300" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="3304" class="Symbol">→</a> <a id="3306" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="Ord.lim"></a><a id="3312" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a>  <a id="3317" class="Symbol">:</a> <a id="3319" class="Symbol">(</a><a id="3320" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3322" class="Symbol">→</a> <a id="3324" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="3327" class="Symbol">)</a> <a id="3329" class="Symbol">→</a> <a id="3331" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
</pre>
这样的 $f : ℕ\rightarrow\text{Ord}$ 又叫做 $\text{lim}\kern{0.17em}f$ 的基本列 (fundamental sequence), 而 $\text{lim}\kern{0.17em}f$ 则叫做基本列 $f$ 的极限. 这样的定义允许我们很方便地讨论零, 后继序数和极限序数三种情况. 为了方便阅读, 我们会把 $\text{zero}$ 写作 $0$, 把 $\text{suc}\kern{0.17em}x$ 写作 $x^+$.

**注意** 我们的序数类型, 学名叫布劳威尔树序数 (Brouwer tree ordinals), 比真正的递归序数宽泛很多, 体现在以下两点:

- 树序数不要求基本列是严格递增的.
  - 严格递增的约束对于计算本身而言无关紧要.
  - 当然, 如果要保证算出的大数足够大, 那么基本列的递增性是必要的.
  - 我们构造的序数的基本列都是严格递增的, 如果想要, 可以额外补上证明.
  - [Agda大序数](https://zhuanlan.zhihu.com/p/572691308)一文中证明了其中构造的上至 $\Gamma_0$ 的所有树序数的基本列都是严格递增的.
- 树序数是高度外延的 (extensional), 即一个真正的递归序数可能对应树上大量的节点.
  - 也就是说我们可以用大量不同的基本列构造出相同的序数.
    - 但同一性证明依赖于函数外延性 (function extensionality), 或某种商 (quotient) 机制, 如 setoid 或 cubical.
  - 但这并不影响大数的计算, 因为只要给出基本列就能算, 况且 FGH 大数的具体数值确实可能是依赖于特定基本列的——同一序数的不同定义方式会使基本列在起始处稍有不同.

**约定** 我们用 $α,β,γ,δ$ 表示序数, 用 $m,n$ 表示自然数.

<pre class="Agda"><a id="4189" class="Keyword">variable</a>
  <a id="4200" href="Veblen.Basic.html#4200" class="Generalizable">α</a> <a id="4202" href="Veblen.Basic.html#4202" class="Generalizable">β</a> <a id="4204" href="Veblen.Basic.html#4204" class="Generalizable">γ</a> <a id="4206" href="Veblen.Basic.html#4206" class="Generalizable">δ</a> <a id="4208" class="Symbol">:</a> <a id="4210" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="4216" href="Veblen.Basic.html#4216" class="Generalizable">m</a> <a id="4218" href="Veblen.Basic.html#4218" class="Generalizable">n</a> <a id="4220" class="Symbol">:</a> <a id="4222" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
</pre>
**约定** 我们遵循类型论的习惯, 今后都会在无歧义的情况下省略函数应用的括号.

**定义** 自然数到序数的嵌入函数 $\text{finord} : ℕ → \text{Ord}$ 如下

$$
\begin{aligned}
\text{finord}\kern{0.17em}0 &= 0 \\
\text{finord}\kern{0.17em}n^+ &= (\text{finord}\kern{0.17em}n)^+
\end{aligned}
$$

<pre class="Agda"><a id="finord"></a><a id="4474" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="4481" class="Symbol">:</a> <a id="4483" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4485" class="Symbol">→</a> <a id="4487" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="4491" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="4498" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4503" class="Symbol">=</a> <a id="4505" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a>
<a id="4510" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="4517" class="Symbol">(</a><a id="4518" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4522" href="Veblen.Basic.html#4522" class="Bound">n</a><a id="4523" class="Symbol">)</a> <a id="4525" class="Symbol">=</a> <a id="4527" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="4531" class="Symbol">(</a><a id="4532" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="4539" href="Veblen.Basic.html#4522" class="Bound">n</a><a id="4540" class="Symbol">)</a>
</pre>
**定义** $\text{finord}$ 构成了基本列 $(0, 1, 2, \ldots)$, 其极限定义为 $ω$

$$
ω := \text{lim}\kern{0.17em}\text{finord}
$$

<pre class="Agda"><a id="ω"></a><a id="4667" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="4669" class="Symbol">=</a> <a id="4671" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4675" href="Veblen.Basic.html#4474" class="Function">finord</a>
</pre>
**非文学** 以下代码调用了[字面量重载](https://agda.readthedocs.io/en/v2.6.4.3-r1/language/literal-overloading.html)功能, 允许数字字面量依据上下文自动具有自然数或序数类型.

<pre class="Agda"><a id="4826" class="Keyword">open</a> <a id="4831" class="Keyword">import</a> <a id="4838" href="Agda.Builtin.FromNat.html" class="Module">Agda.Builtin.FromNat</a> <a id="4859" class="Keyword">public</a>
<a id="4866" class="Keyword">instance</a>
  <a id="nOrd"></a><a id="4877" href="Veblen.Basic.html#4877" class="Function">nOrd</a> <a id="4882" class="Symbol">=</a> <a id="4884" href="Agda.Builtin.FromNat.html#196" class="Record">Number</a> <a id="4891" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="4895" href="Function.Base.html#4486" class="Function Operator">∋</a> <a id="4897" class="Keyword">record</a> <a id="4904" class="Symbol">{</a> <a id="4906" href="Agda.Builtin.FromNat.html#252" class="Field">Constraint</a> <a id="4917" class="Symbol">=</a> <a id="4919" class="Symbol">λ</a> <a id="4921" href="Veblen.Basic.html#4921" class="Bound">_</a> <a id="4923" class="Symbol">→</a> <a id="4925" href="Agda.Builtin.Unit.html#175" class="Record">⊤</a> <a id="4927" class="Symbol">;</a> <a id="4929" href="Agda.Builtin.FromNat.html#281" class="Field">fromNat</a> <a id="4937" class="Symbol">=</a> <a id="4939" class="Symbol">λ</a> <a id="4941" href="Veblen.Basic.html#4941" class="Bound">n</a> <a id="4943" class="Symbol">→</a> <a id="4945" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="4952" href="Veblen.Basic.html#4941" class="Bound">n</a> <a id="4954" class="Symbol">}</a>
  <a id="nNat"></a><a id="4958" href="Veblen.Basic.html#4958" class="Function">nNat</a> <a id="4963" class="Symbol">=</a> <a id="4965" href="Agda.Builtin.FromNat.html#196" class="Record">Number</a> <a id="4972" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>   <a id="4976" href="Function.Base.html#4486" class="Function Operator">∋</a> <a id="4978" class="Keyword">record</a> <a id="4985" class="Symbol">{</a> <a id="4987" href="Agda.Builtin.FromNat.html#252" class="Field">Constraint</a> <a id="4998" class="Symbol">=</a> <a id="5000" class="Symbol">λ</a> <a id="5002" href="Veblen.Basic.html#5002" class="Bound">_</a> <a id="5004" class="Symbol">→</a> <a id="5006" href="Agda.Builtin.Unit.html#175" class="Record">⊤</a> <a id="5008" class="Symbol">;</a> <a id="5010" href="Agda.Builtin.FromNat.html#281" class="Field">fromNat</a> <a id="5018" class="Symbol">=</a> <a id="5020" class="Symbol">λ</a> <a id="5022" href="Veblen.Basic.html#5022" class="Bound">n</a> <a id="5024" class="Symbol">→</a> <a id="5026" href="Veblen.Basic.html#5022" class="Bound">n</a> <a id="5028" class="Symbol">}</a>
</pre>
以下为测试用例.

<pre class="Agda"><a id="5053" href="Veblen.Basic.html#5053" class="Function">_</a> <a id="5055" class="Symbol">=</a> <a id="5057" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5061" href="Function.Base.html#4486" class="Function Operator">∋</a> <a id="5063" class="Number">233</a>
<a id="5067" href="Veblen.Basic.html#5067" class="Function">_</a> <a id="5069" class="Symbol">=</a> <a id="5071" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>   <a id="5075" href="Function.Base.html#4486" class="Function Operator">∋</a> <a id="5077" class="Number">233</a>
</pre>
## 快速增长层级

**约定** 我们用 $A$ 表示类型.

<pre class="Agda"><a id="5127" class="Keyword">variable</a> <a id="5136" href="Veblen.Basic.html#5136" class="Generalizable">A</a> <a id="5138" class="Symbol">:</a> <a id="5140" href="Agda.Primitive.html#388" class="Primitive">Set</a>
</pre>
**定义** 函数 $F : A → A$ 的 $n$ 次复合 $F^n$

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{n^+} &= F \circ F^n
\end{aligned}
$$

其中 $\text{id}$ 是恒等函数.

<pre class="Agda"><a id="_∘ⁿ_"></a><a id="5299" href="Veblen.Basic.html#5299" class="Function Operator">_∘ⁿ_</a> <a id="5304" class="Symbol">:</a> <a id="5306" class="Symbol">(</a><a id="5307" href="Veblen.Basic.html#5136" class="Generalizable">A</a> <a id="5309" class="Symbol">→</a> <a id="5311" href="Veblen.Basic.html#5136" class="Generalizable">A</a><a id="5312" class="Symbol">)</a> <a id="5314" class="Symbol">→</a> <a id="5316" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5318" class="Symbol">→</a> <a id="5320" class="Symbol">(</a><a id="5321" href="Veblen.Basic.html#5136" class="Generalizable">A</a> <a id="5323" class="Symbol">→</a> <a id="5325" href="Veblen.Basic.html#5136" class="Generalizable">A</a><a id="5326" class="Symbol">)</a>
<a id="5328" href="Veblen.Basic.html#5328" class="Bound">F</a> <a id="5330" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="5333" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>  <a id="5339" class="Symbol">=</a> <a id="5341" href="Function.Base.html#704" class="Function">id</a>
<a id="5344" href="Veblen.Basic.html#5344" class="Bound">F</a> <a id="5346" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="5349" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5353" href="Veblen.Basic.html#5353" class="Bound">n</a> <a id="5355" class="Symbol">=</a> <a id="5357" class="Symbol">(</a><a id="5358" href="Veblen.Basic.html#5344" class="Bound">F</a> <a id="5360" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="5362" class="Symbol">(</a><a id="5363" href="Veblen.Basic.html#5344" class="Bound">F</a> <a id="5365" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="5368" href="Veblen.Basic.html#5353" class="Bound">n</a><a id="5369" class="Symbol">))</a>
</pre>
**定义** 快速增长层级 (Fast Growing Hierarchy, FGH) 是一个函数族 $f : \text{Ord} → ℕ → ℕ$, 对于每个序数 $α$, $f_α$ 是一个从自然数到自然数的函数, 定义如下.

$$
\begin{aligned}
f_0\kern{0.17em}n &= n^+ \\
f_{α^+}\kern{0.17em}n &= f_α^n\kern{0.17em}n \\
f_{\text{lim}\kern{0.17em}g}\kern{0.17em}n &= f_{g\kern{0.17em}n}\kern{0.17em}n
\end{aligned}
$$

<pre class="Agda"><a id="5696" class="Keyword">module</a> <a id="FGH"></a><a id="5703" href="Veblen.Basic.html#5703" class="Module">FGH</a> <a id="5707" class="Keyword">where</a>
  <a id="FGH.f"></a><a id="5715" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5717" class="Symbol">:</a> <a id="5719" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5723" class="Symbol">→</a> <a id="5725" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5727" class="Symbol">→</a> <a id="5729" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
  <a id="5733" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5735" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a> <a id="5740" href="Veblen.Basic.html#5740" class="Bound">n</a> <a id="5742" class="Symbol">=</a> <a id="5744" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5748" href="Veblen.Basic.html#5740" class="Bound">n</a>
  <a id="5752" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5754" class="Symbol">(</a><a id="5755" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="5759" href="Veblen.Basic.html#5759" class="Bound">α</a><a id="5760" class="Symbol">)</a> <a id="5762" href="Veblen.Basic.html#5762" class="Bound">n</a> <a id="5764" class="Symbol">=</a> <a id="5766" class="Symbol">(</a><a id="5767" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5769" href="Veblen.Basic.html#5759" class="Bound">α</a> <a id="5771" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="5774" href="Veblen.Basic.html#5762" class="Bound">n</a><a id="5775" class="Symbol">)</a> <a id="5777" href="Veblen.Basic.html#5762" class="Bound">n</a>
  <a id="5781" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5783" class="Symbol">(</a><a id="5784" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="5788" href="Veblen.Basic.html#5788" class="Bound">g</a><a id="5789" class="Symbol">)</a> <a id="5791" href="Veblen.Basic.html#5791" class="Bound">n</a> <a id="5793" class="Symbol">=</a> <a id="5795" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="5797" class="Symbol">(</a><a id="5798" href="Veblen.Basic.html#5788" class="Bound">g</a> <a id="5800" href="Veblen.Basic.html#5791" class="Bound">n</a><a id="5801" class="Symbol">)</a> <a id="5803" href="Veblen.Basic.html#5791" class="Bound">n</a>
</pre>
**例** 我们有

$$
\begin{aligned}
f_0\kern{0.17em}n &= n^+ \\
f_1\kern{0.17em}n &= 2n \\
f_2\kern{0.17em}n &= 2^n\kern{0.17em}n
\end{aligned}
$$

这些等式的证明只需对 $n$ 进行归纳, 是显然的. 代码方面我们只写一些实例作为测试.

<pre class="Agda">  <a id="FGH.f-0-2"></a><a id="6008" href="Veblen.Basic.html#6008" class="Function">f-0-2</a> <a id="6014" class="Symbol">:</a> <a id="6016" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6018" class="Number">0</a> <a id="6020" class="Number">2</a> <a id="6022" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6024" class="Number">3</a>
  <a id="6028" href="Veblen.Basic.html#6008" class="Function">f-0-2</a> <a id="6034" class="Symbol">=</a> <a id="6036" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="FGH.f-1-2"></a><a id="6044" href="Veblen.Basic.html#6044" class="Function">f-1-2</a> <a id="6050" class="Symbol">:</a> <a id="6052" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6054" class="Number">1</a> <a id="6056" class="Number">2</a> <a id="6058" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6060" class="Number">4</a>
  <a id="6064" href="Veblen.Basic.html#6044" class="Function">f-1-2</a> <a id="6070" class="Symbol">=</a> <a id="6072" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="FGH.f-2-2"></a><a id="6080" href="Veblen.Basic.html#6080" class="Function">f-2-2</a> <a id="6086" class="Symbol">:</a> <a id="6088" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6090" class="Number">2</a> <a id="6092" class="Number">2</a> <a id="6094" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6096" class="Number">8</a>
  <a id="6100" href="Veblen.Basic.html#6080" class="Function">f-2-2</a> <a id="6106" class="Symbol">=</a> <a id="6108" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
$f_3$ 以上的表达式越来越复杂, 但不难计算实例如 $f_{3}\kern{0.17em}2=2048$.

<pre class="Agda">  <a id="FGH.f-3-2"></a><a id="6185" href="Veblen.Basic.html#6185" class="Function">f-3-2</a> <a id="6191" class="Symbol">:</a> <a id="6193" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6195" class="Number">3</a> <a id="6197" class="Number">2</a> <a id="6199" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6201" class="Number">2048</a>
  <a id="6208" href="Veblen.Basic.html#6185" class="Function">f-3-2</a> <a id="6214" class="Symbol">=</a> <a id="6216" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**引理** 我们有

$$
\begin{aligned}
f_{\alpha^+}\kern{0.17em}n &= f_\alpha^n\kern{0.17em}n \\
f_{ω}\kern{0.17em}n &= f_{n}\kern{0.17em}n
\end{aligned}
$$

<pre class="Agda">  <a id="FGH.f-suc"></a><a id="6386" href="Veblen.Basic.html#6386" class="Function">f-suc</a> <a id="6392" class="Symbol">:</a> <a id="6394" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6396" class="Symbol">(</a><a id="6397" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="6401" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="6402" class="Symbol">)</a> <a id="6404" href="Veblen.Basic.html#4218" class="Generalizable">n</a> <a id="6406" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6408" class="Symbol">(</a><a id="6409" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6411" href="Veblen.Basic.html#4200" class="Generalizable">α</a> <a id="6413" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="6416" href="Veblen.Basic.html#4218" class="Generalizable">n</a><a id="6417" class="Symbol">)</a> <a id="6419" href="Veblen.Basic.html#4218" class="Generalizable">n</a>
  <a id="6423" href="Veblen.Basic.html#6386" class="Function">f-suc</a> <a id="6429" class="Symbol">=</a> <a id="6431" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="FGH.f-ω"></a><a id="6439" href="Veblen.Basic.html#6439" class="Function">f-ω</a> <a id="6443" class="Symbol">:</a> <a id="6445" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6447" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="6449" href="Veblen.Basic.html#4218" class="Generalizable">n</a> <a id="6451" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6453" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6455" class="Symbol">(</a><a id="6456" href="Veblen.Basic.html#4474" class="Function">finord</a> <a id="6463" href="Veblen.Basic.html#4218" class="Generalizable">n</a><a id="6464" class="Symbol">)</a> <a id="6466" href="Veblen.Basic.html#4218" class="Generalizable">n</a>
  <a id="6470" href="Veblen.Basic.html#6439" class="Function">f-ω</a> <a id="6474" class="Symbol">=</a> <a id="6476" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**注意** 本文出现的大部分命题的证明都是「依定义即得」的, 体现为代码中的 `refl`. 也就是说, 证明都是直接展开定义, 不需要额外的推理. 但这并不意味着所有证明是显然的, 有时候递归定义的展开会非常复杂, 这时候我们会分步展开, 逐步化简, 但每一步都 `refl` 可证.

**定理** 由以上两式不难看出

$$
f_{ω^+}\kern{0.17em}n = f_ω^n\kern{0.17em}n
$$

<pre class="Agda">  <a id="FGH.f-ω⁺"></a><a id="6711" href="Veblen.Basic.html#6711" class="Function">f-ω⁺</a> <a id="6716" class="Symbol">:</a> <a id="6718" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6720" class="Symbol">(</a><a id="6721" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="6725" href="Veblen.Basic.html#4667" class="Function">ω</a><a id="6726" class="Symbol">)</a> <a id="6728" href="Veblen.Basic.html#4218" class="Generalizable">n</a> <a id="6730" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6732" class="Symbol">(</a><a id="6733" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="6735" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="6737" href="Veblen.Basic.html#5299" class="Function Operator">∘ⁿ</a> <a id="6740" href="Veblen.Basic.html#4218" class="Generalizable">n</a><a id="6741" class="Symbol">)</a> <a id="6743" href="Veblen.Basic.html#4218" class="Generalizable">n</a>
  <a id="6747" href="Veblen.Basic.html#6711" class="Function">f-ω⁺</a> <a id="6752" class="Symbol">=</a> <a id="6754" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**推论** 特别地, 有

$$
f_{ω^+}\kern{0.17em}2 = f_ω\kern{0.17em}(f_ω\kern{0.17em}2)
$$

但此式无法在 Agda 中直接证明, 因为 Agda 想先把两边都算出再比较相等, 而这是不现实的. 如果有读者知道如何证明, 请打在评论区. 作为替代, 我们可以证明如下式子.

$$
f_{\alpha^+}\kern{0.17em}2 = f_\alpha\kern{0.17em}(f_\alpha\kern{0.17em}2)
$$

<pre class="Agda">  <a id="FGH.f-suc-2"></a><a id="7029" href="Veblen.Basic.html#7029" class="Function">f-suc-2</a> <a id="7037" class="Symbol">:</a> <a id="7039" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="7041" class="Symbol">(</a><a id="7042" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="7046" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="7047" class="Symbol">)</a> <a id="7049" class="Number">2</a> <a id="7051" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7053" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="7055" href="Veblen.Basic.html#4200" class="Generalizable">α</a> <a id="7057" class="Symbol">(</a><a id="7058" href="Veblen.Basic.html#5715" class="Function">f</a> <a id="7060" href="Veblen.Basic.html#4200" class="Generalizable">α</a> <a id="7062" class="Number">2</a><a id="7063" class="Symbol">)</a>
  <a id="7067" href="Veblen.Basic.html#7029" class="Function">f-suc-2</a> <a id="7075" class="Symbol">=</a> <a id="7077" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**事实** $f_{ω^+} 64$ 已经大于葛立恒数.

> 从这里开始, 研究大数的数学就转变成了研究快速增长函数的数学, 进而转变成研究大的序数的数学.

## 序数的递归原理

为了系统性的构造大序数, 我们先证明序数归纳法, 并由此得到序数的递归原理.

**定理 序数归纳法 (transfinite induction)** 对于任意性质 $P : \text{Ord} → \text{Set}$, 如果

1. $P\kern{0.17em}0$ 成立,
2. 对于任意序数 $α$, 如果 $P\kern{0.17em}α$ 成立, 则 $P\kern{0.17em}α^+$ 成立,
3. 对于任意基本列 $f$, 如果对于任意自然数 $n$, $P\kern{0.17em}(f\kern{0.17em}n)$ 成立, 则 $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立,

则对于任意序数 $α$, $P\kern{0.17em}α$ 成立.

<pre class="Agda"><a id="ind"></a><a id="7554" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="7558" class="Symbol">:</a> <a id="7560" class="Symbol">{</a><a id="7561" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7563" class="Symbol">:</a> <a id="7565" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7569" class="Symbol">→</a> <a id="7571" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="7574" class="Symbol">}</a>
  <a id="7578" class="Symbol">→</a> <a id="7580" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7582" class="InductiveConstructor">zero</a>
  <a id="7589" class="Symbol">→</a> <a id="7591" class="Symbol">(∀</a> <a id="7594" href="Veblen.Basic.html#7594" class="Bound">α</a> <a id="7596" class="Symbol">→</a> <a id="7598" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7600" href="Veblen.Basic.html#7594" class="Bound">α</a> <a id="7602" class="Symbol">→</a> <a id="7604" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7606" class="Symbol">(</a><a id="7607" class="InductiveConstructor">suc</a> <a id="7611" href="Veblen.Basic.html#7594" class="Bound">α</a><a id="7612" class="Symbol">))</a>
  <a id="7617" class="Symbol">→</a> <a id="7619" class="Symbol">(∀</a> <a id="7622" href="Veblen.Basic.html#7622" class="Bound">f</a> <a id="7624" class="Symbol">→</a> <a id="7626" class="Symbol">(∀</a> <a id="7629" href="Veblen.Basic.html#7629" class="Bound">n</a> <a id="7631" class="Symbol">→</a> <a id="7633" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7635" class="Symbol">(</a><a id="7636" href="Veblen.Basic.html#7622" class="Bound">f</a> <a id="7638" href="Veblen.Basic.html#7629" class="Bound">n</a><a id="7639" class="Symbol">))</a> <a id="7642" class="Symbol">→</a> <a id="7644" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7646" class="Symbol">(</a><a id="7647" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="7651" href="Veblen.Basic.html#7622" class="Bound">f</a><a id="7652" class="Symbol">))</a>
  <a id="7657" class="Symbol">→</a> <a id="7659" class="Symbol">∀</a> <a id="7661" href="Veblen.Basic.html#7661" class="Bound">α</a> <a id="7663" class="Symbol">→</a> <a id="7665" href="Veblen.Basic.html#7561" class="Bound">P</a> <a id="7667" href="Veblen.Basic.html#7661" class="Bound">α</a>
</pre>
**(证明)** 要证对于任意序数 $α$, $P\kern{0.17em}α$ 成立. 归纳 $α$ 的三种情况.

- 当 $α=0$ 时, 由条件1, $P\kern{0.17em}0$ 成立.
- 当 $α=α^+$ 时, 要证 $P\,α^+$ 成立. 由归纳假设, $P\kern{0.17em}α$ 成立. 由条件2, $P\kern{0.17em}α^+$ 成立.
- 当 $α=\text{lim}\kern{0.17em}f$ 时, 要证 $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立. 由归纳假设, 对于任意自然数 $n$, $P\kern{0.17em}(f\kern{0.17em}n)$ 成立. 由条件3, $P\kern{0.17em}(\text{lim}\kern{0.17em}f)$ 成立. ∎

<pre class="Agda"><a id="8073" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="8077" href="Veblen.Basic.html#8077" class="Bound">z</a> <a id="8079" href="Veblen.Basic.html#8079" class="Bound">s</a> <a id="8081" href="Veblen.Basic.html#8081" class="Bound">l</a> <a id="8083" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a> <a id="8088" class="Symbol">=</a> <a id="8090" href="Veblen.Basic.html#8077" class="Bound">z</a>
<a id="8092" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="8096" href="Veblen.Basic.html#8096" class="Bound">z</a> <a id="8098" href="Veblen.Basic.html#8098" class="Bound">s</a> <a id="8100" href="Veblen.Basic.html#8100" class="Bound">l</a> <a id="8102" class="Symbol">(</a><a id="8103" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="8107" href="Veblen.Basic.html#8107" class="Bound">α</a><a id="8108" class="Symbol">)</a> <a id="8110" class="Symbol">=</a> <a id="8112" href="Veblen.Basic.html#8098" class="Bound">s</a> <a id="8114" href="Veblen.Basic.html#8107" class="Bound">α</a> <a id="8116" class="Symbol">(</a><a id="8117" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="8121" href="Veblen.Basic.html#8096" class="Bound">z</a> <a id="8123" href="Veblen.Basic.html#8098" class="Bound">s</a> <a id="8125" href="Veblen.Basic.html#8100" class="Bound">l</a> <a id="8127" href="Veblen.Basic.html#8107" class="Bound">α</a><a id="8128" class="Symbol">)</a>
<a id="8130" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="8134" href="Veblen.Basic.html#8134" class="Bound">z</a> <a id="8136" href="Veblen.Basic.html#8136" class="Bound">s</a> <a id="8138" href="Veblen.Basic.html#8138" class="Bound">l</a> <a id="8140" class="Symbol">(</a><a id="8141" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="8145" href="Veblen.Basic.html#8145" class="Bound">f</a><a id="8146" class="Symbol">)</a> <a id="8148" class="Symbol">=</a> <a id="8150" href="Veblen.Basic.html#8138" class="Bound">l</a> <a id="8152" href="Veblen.Basic.html#8145" class="Bound">f</a> <a id="8154" class="Symbol">λ</a> <a id="8156" href="Veblen.Basic.html#8156" class="Bound">n</a> <a id="8158" class="Symbol">→</a> <a id="8160" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="8164" href="Veblen.Basic.html#8134" class="Bound">z</a> <a id="8166" href="Veblen.Basic.html#8136" class="Bound">s</a> <a id="8168" href="Veblen.Basic.html#8138" class="Bound">l</a> <a id="8170" class="Symbol">(</a><a id="8171" href="Veblen.Basic.html#8145" class="Bound">f</a> <a id="8173" href="Veblen.Basic.html#8156" class="Bound">n</a><a id="8174" class="Symbol">)</a>
</pre>
**注意** 这里看起来像是循环论证, 我们实际做的事情是从类型论承诺的规则中抽取出对 $\text{Ord}$ 单独适用的部分, 并固化为了一个高阶函数 $\text{ind}$.

**定理 序数的递归原理 (transfinite recursion)** 对于任意类型 $A$, 函数 $z : A$, $s : A → A$, $l : (ℕ → A) → A$, 和任意序数 $α$, 存在唯一的 $\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α : A$, 满足

$$
\begin{aligned}
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}0 &= z \\
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α^+ &= s\kern{0.17em}(\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}α) \\
\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}(\text{lim}\kern{0.17em}f) &= l\kern{0.17em}(λ\kern{0.17em}n,\text{rec}\kern{0.17em}z\kern{0.17em}s\kern{0.17em}l\kern{0.17em}(f\kern{0.17em}n))
\end{aligned}
$$

**(证明)** 令 $P = λ\kern{0.17em}\_,A$ 并应用序数归纳法即可. ∎

<pre class="Agda"><a id="rec"></a><a id="9003" href="Veblen.Basic.html#9003" class="Function">rec</a> <a id="9007" class="Symbol">:</a> <a id="9009" href="Veblen.Basic.html#5136" class="Generalizable">A</a> <a id="9011" class="Symbol">→</a> <a id="9013" class="Symbol">(</a><a id="9014" href="Veblen.Basic.html#5136" class="Generalizable">A</a> <a id="9016" class="Symbol">→</a> <a id="9018" href="Veblen.Basic.html#5136" class="Generalizable">A</a><a id="9019" class="Symbol">)</a> <a id="9021" class="Symbol">→</a> <a id="9023" class="Symbol">((</a><a id="9025" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9027" class="Symbol">→</a> <a id="9029" href="Veblen.Basic.html#5136" class="Generalizable">A</a><a id="9030" class="Symbol">)</a> <a id="9032" class="Symbol">→</a> <a id="9034" href="Veblen.Basic.html#5136" class="Generalizable">A</a><a id="9035" class="Symbol">)</a> <a id="9037" class="Symbol">→</a> <a id="9039" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="9043" class="Symbol">→</a> <a id="9045" href="Veblen.Basic.html#5136" class="Generalizable">A</a>
<a id="9047" href="Veblen.Basic.html#9003" class="Function">rec</a> <a id="9051" href="Veblen.Basic.html#9051" class="Bound">z</a> <a id="9053" href="Veblen.Basic.html#9053" class="Bound">s</a> <a id="9055" href="Veblen.Basic.html#9055" class="Bound">l</a> <a id="9057" class="Symbol">=</a> <a id="9059" href="Veblen.Basic.html#7554" class="Function">ind</a> <a id="9063" href="Veblen.Basic.html#9051" class="Bound">z</a> <a id="9065" class="Symbol">(λ</a> <a id="9068" href="Veblen.Basic.html#9068" class="Bound">_</a> <a id="9070" class="Symbol">→</a> <a id="9072" href="Veblen.Basic.html#9053" class="Bound">s</a><a id="9073" class="Symbol">)</a> <a id="9075" class="Symbol">(λ</a> <a id="9078" href="Veblen.Basic.html#9078" class="Bound">_</a> <a id="9080" class="Symbol">→</a> <a id="9082" href="Veblen.Basic.html#9055" class="Bound">l</a><a id="9083" class="Symbol">)</a>
</pre>
**注意** 序数的递归原理和序数归纳法都可视作高阶函数, 递归原理是归纳法的特例.

**注意** 序数的递归原理相当强大, 因为 $A$ 可以是任意类型, 包括函数类型 $\text{Ord}\rightarrow\text{Ord}$ 与 $(\text{Ord}\rightarrow\text{Ord})\rightarrow(\text{Ord}\rightarrow\text{Ord})$ 等, 也就是说它允许定义高阶函数的递归. 本文出现的所有大序数都由 $\text{rec}$ 定义.

## 超限复合

**约定** 我们用 $F$ 表示序数函数 $\text{Ord} → \text{Ord}$, 用 $f,g,h$ 表示基本列 $ℕ → \text{Ord}$.

<pre class="Agda"><a id="9446" class="Keyword">variable</a>
  <a id="9457" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="9459" class="Symbol">:</a> <a id="9461" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="9465" class="Symbol">→</a> <a id="9467" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="9473" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="9475" href="Veblen.Basic.html#9475" class="Generalizable">g</a> <a id="9477" href="Veblen.Basic.html#9477" class="Generalizable">h</a> <a id="9479" class="Symbol">:</a> <a id="9481" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9483" class="Symbol">→</a> <a id="9485" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
</pre>
**定义** 仿照函数 $F : A → A$ 的 $n$ 次复合 $F^n$, 我们定义序数函数 $F : \text{Ord} → \text{Ord}$ 的 $α$ 次复合 $F^α$, 但使用序数的递归原理 $\text{rec}$ 来定义.

$$
F^\alpha\kern{0.17em}\beta=\text{rec}\kern{0.17em}\beta\kern{0.17em}F\kern{0.17em}\text{lim}\kern{0.17em}\alpha
$$

<pre class="Agda"><a id="_∘^_"></a><a id="9748" href="Veblen.Basic.html#9748" class="Function Operator">_∘^_</a> <a id="9753" class="Symbol">:</a> <a id="9755" class="Symbol">(</a><a id="9756" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="9760" class="Symbol">→</a> <a id="9762" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="9765" class="Symbol">)</a> <a id="9767" class="Symbol">→</a> <a id="9769" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="9773" class="Symbol">→</a> <a id="9775" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="9779" class="Symbol">→</a> <a id="9781" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="9785" class="Symbol">(</a><a id="9786" href="Veblen.Basic.html#9786" class="Bound">F</a> <a id="9788" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="9791" href="Veblen.Basic.html#9791" class="Bound">α</a><a id="9792" class="Symbol">)</a> <a id="9794" href="Veblen.Basic.html#9794" class="Bound">β</a> <a id="9796" class="Symbol">=</a> <a id="9798" href="Veblen.Basic.html#9003" class="Function">rec</a> <a id="9802" href="Veblen.Basic.html#9794" class="Bound">β</a> <a id="9804" href="Veblen.Basic.html#9786" class="Bound">F</a> <a id="9806" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9810" href="Veblen.Basic.html#9791" class="Bound">α</a>
</pre>
**注意** 该定义不是 $F^\alpha\kern{0.17em}\beta=\text{rec}\kern{0.17em}\beta\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}\alpha)$, 此式有类型错误.

对于 $\text{rec}$ 的四个参数, 直观上

- 第一个参数是初始值, 这里是 $F^\alpha$ 的输入 $\beta$,
- 第二个参数是后继步骤, 需要指定递归迭代的函数, 这里递归迭代的就是 $F$,
- 第三个参数是极限步骤, 需要指定将极限步对应的步骤基本列 $λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta$ 映射到序数的函数, 这里就是单纯地取其极限, 所以指定为 $\text{lim}$,
- 第四个参数是递归的次数, 这里是 $\alpha$.

**定理** 依定义有

$$
\begin{aligned}
F^0 &= \text{id} \\
F^{α^+} &= F \circ F^α \\
F^{\text{lim}\kern{0.17em}f} &= λ\kern{0.17em}\beta,\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta
\end{aligned}
$$

<pre class="Agda"><a id="∘^-zero"></a><a id="10513" href="Veblen.Basic.html#10513" class="Function">∘^-zero</a> <a id="10521" class="Symbol">:</a> <a id="10523" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10525" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="10528" class="InductiveConstructor">zero</a> <a id="10533" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10535" href="Function.Base.html#704" class="Function">id</a>
<a id="10538" href="Veblen.Basic.html#10513" class="Function">∘^-zero</a> <a id="10546" class="Symbol">=</a> <a id="10548" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="∘^-suc"></a><a id="10554" href="Veblen.Basic.html#10554" class="Function">∘^-suc</a> <a id="10561" class="Symbol">:</a> <a id="10563" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10565" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="10568" class="InductiveConstructor">suc</a> <a id="10572" href="Veblen.Basic.html#4200" class="Generalizable">α</a> <a id="10574" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10576" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10578" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="10580" class="Symbol">(</a><a id="10581" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10583" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="10586" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="10587" class="Symbol">)</a>
<a id="10589" href="Veblen.Basic.html#10554" class="Function">∘^-suc</a> <a id="10596" class="Symbol">=</a> <a id="10598" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="∘^-lim"></a><a id="10604" href="Veblen.Basic.html#10604" class="Function">∘^-lim</a> <a id="10611" class="Symbol">:</a> <a id="10613" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10615" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="10618" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="10622" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="10624" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10626" class="Symbol">λ</a> <a id="10628" href="Veblen.Basic.html#10628" class="Bound">β</a> <a id="10630" class="Symbol">→</a> <a id="10632" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="10636" class="Symbol">λ</a> <a id="10638" href="Veblen.Basic.html#10638" class="Bound">n</a> <a id="10640" class="Symbol">→</a> <a id="10642" class="Symbol">(</a><a id="10643" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="10645" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="10648" class="Symbol">(</a><a id="10649" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="10651" href="Veblen.Basic.html#10638" class="Bound">n</a><a id="10652" class="Symbol">))</a> <a id="10655" href="Veblen.Basic.html#10628" class="Bound">β</a>
<a id="10657" href="Veblen.Basic.html#10604" class="Function">∘^-lim</a> <a id="10664" class="Symbol">=</a> <a id="10666" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**注意** $λ\kern{0.17em}\beta,\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}\kern{0.17em}\beta$ 不能简化成 $\text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}F^{f\kern{0.17em}n}$, 此式有类型错误.

## 序数算术

**定义** 从 $α$ 开始做 $β$ 次后继叫做序数加法, 记作 $α+β$.

<pre class="Agda"><a id="10972" class="Keyword">infixl</a> <a id="10979" class="Number">6</a> <a id="10981" href="Veblen.Basic.html#10985" class="Function Operator">_+_</a>
<a id="_+_"></a><a id="10985" href="Veblen.Basic.html#10985" class="Function Operator">_+_</a> <a id="10989" class="Symbol">:</a> <a id="10991" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10995" class="Symbol">→</a> <a id="10997" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11001" class="Symbol">→</a> <a id="11003" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="11007" href="Veblen.Basic.html#11007" class="Bound">α</a> <a id="11009" href="Veblen.Basic.html#10985" class="Function Operator">+</a> <a id="11011" href="Veblen.Basic.html#11011" class="Bound">β</a> <a id="11013" class="Symbol">=</a> <a id="11015" class="Symbol">(</a><a id="11016" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="11020" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="11023" href="Veblen.Basic.html#11011" class="Bound">β</a><a id="11024" class="Symbol">)</a> <a id="11026" href="Veblen.Basic.html#11007" class="Bound">α</a>
</pre>
**定义** 从 $0$ 开始做 $β$ 次 $+ α$ 叫做序数乘法, 记作 $α*β$.

<pre class="Agda"><a id="11089" class="Keyword">infixl</a> <a id="11096" class="Number">7</a> <a id="11098" href="Veblen.Basic.html#11102" class="Function Operator">_*_</a>
<a id="_*_"></a><a id="11102" href="Veblen.Basic.html#11102" class="Function Operator">_*_</a> <a id="11106" class="Symbol">:</a> <a id="11108" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11112" class="Symbol">→</a> <a id="11114" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11118" class="Symbol">→</a> <a id="11120" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="11124" href="Veblen.Basic.html#11124" class="Bound">α</a> <a id="11126" href="Veblen.Basic.html#11102" class="Function Operator">*</a> <a id="11128" href="Veblen.Basic.html#11128" class="Bound">β</a> <a id="11130" class="Symbol">=</a> <a id="11132" class="Symbol">((</a><a id="11134" href="Veblen.Basic.html#10985" class="Function Operator">_+</a> <a id="11137" href="Veblen.Basic.html#11124" class="Bound">α</a><a id="11138" class="Symbol">)</a> <a id="11140" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="11143" href="Veblen.Basic.html#11128" class="Bound">β</a><a id="11144" class="Symbol">)</a> <a id="11146" class="Number">0</a>
</pre>
**定义** 从 $1$ 开始做 $β$ 次 $* α$ 叫做序数幂, 记作 $α^β$.

<pre class="Agda"><a id="11208" class="Keyword">infix</a> <a id="11214" class="Number">8</a> <a id="11216" href="Veblen.Basic.html#11220" class="Function Operator">_^_</a>
<a id="_^_"></a><a id="11220" href="Veblen.Basic.html#11220" class="Function Operator">_^_</a> <a id="11224" class="Symbol">:</a> <a id="11226" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11230" class="Symbol">→</a> <a id="11232" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11236" class="Symbol">→</a> <a id="11238" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="11242" href="Veblen.Basic.html#11242" class="Bound">α</a> <a id="11244" href="Veblen.Basic.html#11220" class="Function Operator">^</a> <a id="11246" href="Veblen.Basic.html#11246" class="Bound">β</a> <a id="11248" class="Symbol">=</a> <a id="11250" class="Symbol">((</a><a id="11252" href="Veblen.Basic.html#11102" class="Function Operator">_*</a> <a id="11255" href="Veblen.Basic.html#11242" class="Bound">α</a><a id="11256" class="Symbol">)</a> <a id="11258" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="11261" href="Veblen.Basic.html#11246" class="Bound">β</a><a id="11262" class="Symbol">)</a> <a id="11264" class="Number">1</a>
</pre>
关于为什么不能定义序数的第四级运算的原因可以参看[Agda大序数(6) 迭代幂次](https://zhuanlan.zhihu.com/p/580526275).

## 三大高阶函数

Veblen层级的构造需要三个重要的高阶函数

1. 无穷迭代 $λF,F^\omega$
2. 跳出运算 $\text{jump}$
3. 不动点的枚举 $\text{fixpt}$

它们都具有类型 $(\text{Ord}→\text{Ord})→(\text{Ord}→\text{Ord})$.

### 无穷迭代

**定义** 我们称 $F$ 的 $\omega$ 次复合 $F^\omega$ 为 $F$ 的无穷迭代.

<pre class="Agda"><a id="iterω"></a><a id="11593" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="11599" class="Symbol">:</a> <a id="11601" class="Symbol">(</a><a id="11602" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11606" class="Symbol">→</a> <a id="11608" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="11611" class="Symbol">)</a> <a id="11613" class="Symbol">→</a> <a id="11615" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11619" class="Symbol">→</a> <a id="11621" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="11625" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="11631" href="Veblen.Basic.html#11631" class="Bound">F</a> <a id="11633" class="Symbol">=</a> <a id="11635" href="Veblen.Basic.html#11631" class="Bound">F</a> <a id="11637" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="11640" href="Veblen.Basic.html#4667" class="Function">ω</a>
</pre>
### 跳出运算

**定义** 给定序数函数 $F$ 和迭代次数 $α$, 从 $F\kern{0.17em}0$ 开始, 每次迭代时先做一次后继再迭代 $F$, 总共迭代 $α$ 次的运算叫做 $F$ 的 $α$ 次跳出, 记作 $\text{jump}\kern{0.17em}F\kern{0.17em}α$.

$$
\text{jump}\kern{0.17em}F\kern{0.17em}α := (F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^α\kern{0.17em}(F\kern{0.17em}0)
$$

<pre class="Agda"><a id="jump"></a><a id="11956" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="11961" class="Symbol">:</a> <a id="11963" class="Symbol">(</a><a id="11964" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11968" class="Symbol">→</a> <a id="11970" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="11973" class="Symbol">)</a> <a id="11975" class="Symbol">→</a> <a id="11977" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="11981" class="Symbol">→</a> <a id="11983" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="11987" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="11992" href="Veblen.Basic.html#11992" class="Bound">F</a> <a id="11994" href="Veblen.Basic.html#11994" class="Bound">α</a> <a id="11996" class="Symbol">=</a> <a id="11998" class="Symbol">((</a><a id="12000" href="Veblen.Basic.html#11992" class="Bound">F</a> <a id="12002" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="12004" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a><a id="12007" class="Symbol">)</a> <a id="12009" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="12012" href="Veblen.Basic.html#11994" class="Bound">α</a><a id="12013" class="Symbol">)</a> <a id="12015" class="Symbol">(</a><a id="12016" href="Veblen.Basic.html#11992" class="Bound">F</a> <a id="12018" class="Number">0</a><a id="12019" class="Symbol">)</a>
</pre>
**定理** 依定义有

$$
\begin{aligned}
\text{jump}\kern{0.17em}F\kern{0.17em}0 &= F\kern{0.17em}0 \\
\text{jump}\kern{0.17em}F\kern{0.17em}(α^+) &= F\kern{0.17em}(\text{jump}\kern{0.17em}F\kern{0.17em}α)^+ \\
\text{jump}\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}f) &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\text{jump}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)
\end{aligned}
$$

**(证明)** 零和极限的情况是显然的. 对于后继的情况, 有

$$
\begin{aligned}
\text{jump}\kern{0.17em}F\kern{0.17em}(α^+) &= (F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^{α^+}\kern{0.17em}(F\kern{0.17em}0) \\
&= (F\kern{0.17em}\circ\kern{0.17em}\text{suc})((F\kern{0.17em}\circ\kern{0.17em}\text{suc})\kern{0.17em}^α\kern{0.17em}(F\kern{0.17em}0)) \\
&= F\kern{0.17em}(\text{jump}\kern{0.17em}F\kern{0.17em}α)^+
\end{aligned}
$$

∎

<pre class="Agda"><a id="jump-0"></a><a id="12864" href="Veblen.Basic.html#12864" class="Function">jump-0</a> <a id="12871" class="Symbol">:</a> <a id="12873" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="12878" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="12880" class="Number">0</a> <a id="12882" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12884" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="12886" class="Number">0</a>
<a id="12888" href="Veblen.Basic.html#12864" class="Function">jump-0</a> <a id="12895" class="Symbol">=</a> <a id="12897" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="jump-suc"></a><a id="12903" href="Veblen.Basic.html#12903" class="Function">jump-suc</a> <a id="12912" class="Symbol">:</a> <a id="12914" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="12919" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="12921" class="Symbol">(</a><a id="12922" class="InductiveConstructor">suc</a> <a id="12926" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="12927" class="Symbol">)</a> <a id="12929" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12931" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="12933" class="Symbol">(</a><a id="12934" class="InductiveConstructor">suc</a> <a id="12938" class="Symbol">(</a><a id="12939" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="12944" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="12946" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="12947" class="Symbol">))</a>
<a id="12950" href="Veblen.Basic.html#12903" class="Function">jump-suc</a> <a id="12959" class="Symbol">{</a><a id="12960" href="Veblen.Basic.html#12960" class="Bound">F</a><a id="12961" class="Symbol">}</a> <a id="12963" class="Symbol">{</a><a id="12964" href="Veblen.Basic.html#12964" class="Bound">α</a><a id="12965" class="Symbol">}</a> <a id="12967" class="Symbol">=</a> <a id="12969" href="Relation.Binary.Reasoning.Syntax.html#1510" class="Function Operator">begin</a>
  <a id="12977" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="12982" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="12984" class="Symbol">(</a><a id="12985" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12989" href="Veblen.Basic.html#12964" class="Bound">α</a><a id="12990" class="Symbol">)</a>                        <a id="13015" href="Relation.Binary.Reasoning.Syntax.html#11017" class="Function">≡⟨⟩</a>
  <a id="13021" class="Symbol">((</a><a id="13023" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13025" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="13027" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a><a id="13030" class="Symbol">)</a> <a id="13032" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="13035" class="Symbol">(</a><a id="13036" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13040" href="Veblen.Basic.html#12964" class="Bound">α</a><a id="13041" class="Symbol">))</a> <a id="13044" class="Symbol">(</a><a id="13045" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13047" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13051" class="Symbol">)</a>       <a id="13059" href="Relation.Binary.Reasoning.Syntax.html#11017" class="Function">≡⟨⟩</a>
  <a id="13065" class="Symbol">(</a><a id="13066" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13068" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="13070" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a><a id="13073" class="Symbol">)</a> <a id="13075" class="Symbol">(((</a><a id="13078" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13080" href="Function.Base.html#1115" class="Function Operator">∘</a> <a id="13082" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a><a id="13085" class="Symbol">)</a> <a id="13087" href="Veblen.Basic.html#9748" class="Function Operator">∘^</a> <a id="13090" href="Veblen.Basic.html#12964" class="Bound">α</a><a id="13091" class="Symbol">)</a> <a id="13093" class="Symbol">(</a><a id="13094" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13096" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13100" class="Symbol">))</a> <a id="13103" href="Relation.Binary.Reasoning.Syntax.html#11017" class="Function">≡⟨⟩</a>
  <a id="13109" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13111" class="Symbol">(</a><a id="13112" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13116" class="Symbol">(</a><a id="13117" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="13122" href="Veblen.Basic.html#12960" class="Bound">F</a> <a id="13124" href="Veblen.Basic.html#12964" class="Bound">α</a><a id="13125" class="Symbol">))</a>                    <a id="13147" href="Relation.Binary.Reasoning.Syntax.html#12283" class="Function Operator">∎</a>

<a id="jump-lim"></a><a id="13150" href="Veblen.Basic.html#13150" class="Function">jump-lim</a> <a id="13159" class="Symbol">:</a> <a id="13161" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="13166" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="13168" class="Symbol">(</a><a id="13169" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13173" href="Veblen.Basic.html#9473" class="Generalizable">f</a><a id="13174" class="Symbol">)</a> <a id="13176" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="13178" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13182" class="Symbol">λ</a> <a id="13184" href="Veblen.Basic.html#13184" class="Bound">n</a> <a id="13186" class="Symbol">→</a> <a id="13188" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="13193" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="13195" class="Symbol">(</a><a id="13196" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="13198" href="Veblen.Basic.html#13184" class="Bound">n</a><a id="13199" class="Symbol">)</a>
<a id="13201" href="Veblen.Basic.html#13150" class="Function">jump-lim</a> <a id="13210" class="Symbol">=</a> <a id="13212" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
### 不动点的枚举

**定义** 给定序数函数 $F$, 我们定义 $F$ 的第 $α$ 个不动点 $\text{fixpt}\kern{0.17em}F\kern{0.17em}α$ 为 $F^\omega$ 的第 $α$ 个跳出 $\text{jump}\kern{0.17em}(F^\omega)\kern{0.17em}α$.

$$
\text{fixpt}\kern{0.17em}F := \text{jump}\kern{0.17em}(F^\omega)
$$

<pre class="Agda"><a id="fixpt"></a><a id="13474" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="13480" class="Symbol">:</a> <a id="13482" class="Symbol">(</a><a id="13483" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="13487" class="Symbol">→</a> <a id="13489" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="13492" class="Symbol">)</a> <a id="13494" class="Symbol">→</a> <a id="13496" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="13500" class="Symbol">→</a> <a id="13502" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="13506" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="13512" href="Veblen.Basic.html#13512" class="Bound">F</a> <a id="13514" class="Symbol">=</a> <a id="13516" href="Veblen.Basic.html#11956" class="Function">jump</a> <a id="13521" class="Symbol">(</a><a id="13522" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="13528" href="Veblen.Basic.html#13512" class="Bound">F</a><a id="13529" class="Symbol">)</a>
</pre>
**定理** 依定义有

$$
\begin{aligned}
\text{fixpt}\kern{0.17em}F\kern{0.17em}0 &= F^\omega\kern{0.17em}0 \\
\text{fixpt}\kern{0.17em}F\kern{0.17em}(α^+) &= F^\omega\kern{0.17em}(\text{fixpt}\kern{0.17em}F\kern{0.17em}α)^+ \\
\text{fixpt}\kern{0.17em}F\kern{0.17em}(\text{lim}\kern{0.17em}f) &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\text{fixpt}\kern{0.17em}F\kern{0.17em}(f\kern{0.17em}n)
\end{aligned}
$$

<pre class="Agda"><a id="fixpt-0"></a><a id="13972" href="Veblen.Basic.html#13972" class="Function">fixpt-0</a> <a id="13980" class="Symbol">:</a> <a id="13982" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="13988" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="13990" class="Number">0</a> <a id="13992" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="13994" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="14000" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14002" class="Number">0</a>
<a id="14004" href="Veblen.Basic.html#13972" class="Function">fixpt-0</a> <a id="14012" class="Symbol">=</a> <a id="14014" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="fixpt-suc"></a><a id="14020" href="Veblen.Basic.html#14020" class="Function">fixpt-suc</a> <a id="14030" class="Symbol">:</a> <a id="14032" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="14038" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14040" class="Symbol">(</a><a id="14041" class="InductiveConstructor">suc</a> <a id="14045" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="14046" class="Symbol">)</a> <a id="14048" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="14050" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="14056" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14058" class="Symbol">(</a><a id="14059" class="InductiveConstructor">suc</a> <a id="14063" class="Symbol">(</a><a id="14064" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="14070" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14072" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="14073" class="Symbol">))</a>
<a id="14076" href="Veblen.Basic.html#14020" class="Function">fixpt-suc</a> <a id="14086" class="Symbol">{</a><a id="14087" href="Veblen.Basic.html#14087" class="Bound">F</a><a id="14088" class="Symbol">}</a> <a id="14090" class="Symbol">{</a><a id="14091" href="Veblen.Basic.html#14091" class="Bound">α</a><a id="14092" class="Symbol">}</a> <a id="14094" class="Symbol">=</a> <a id="14096" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="fixpt-lim"></a><a id="14102" href="Veblen.Basic.html#14102" class="Function">fixpt-lim</a> <a id="14112" class="Symbol">:</a> <a id="14114" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="14120" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14122" class="Symbol">(</a><a id="14123" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="14127" href="Veblen.Basic.html#9473" class="Generalizable">f</a><a id="14128" class="Symbol">)</a> <a id="14130" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="14132" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="14136" class="Symbol">λ</a> <a id="14138" href="Veblen.Basic.html#14138" class="Bound">n</a> <a id="14140" class="Symbol">→</a> <a id="14142" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="14148" href="Veblen.Basic.html#9457" class="Generalizable">F</a> <a id="14150" class="Symbol">(</a><a id="14151" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="14153" href="Veblen.Basic.html#14138" class="Bound">n</a><a id="14154" class="Symbol">)</a>
<a id="14156" href="Veblen.Basic.html#14102" class="Function">fixpt-lim</a> <a id="14166" class="Symbol">=</a> <a id="14168" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**注意** 跳出运算并非一定搭配无穷迭代使用, 后面会出现多种情况需要跳出, 以提高增长率.

## ε， ζ， η 层级

我们定义三个序数函数 $\varepsilon, \zeta, \eta$ 如下.

**定义** $\varepsilon$ 是函数 $λα,ω^α$ 的不动点枚举

$$
ε := \text{fixpt}\kern{0.17em}λα,ω\kern{0.17em}^α
$$

<pre class="Agda"><a id="ε"></a><a id="14392" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14394" class="Symbol">:</a> <a id="14396" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="14400" class="Symbol">→</a> <a id="14402" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="14406" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14408" class="Symbol">=</a> <a id="14410" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="14416" class="Symbol">(</a><a id="14417" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="14419" href="Veblen.Basic.html#11220" class="Function Operator">^_</a><a id="14421" class="Symbol">)</a>
</pre>
**定理** 依定义有

$$
\begin{aligned}
\varepsilon_0 &= (λα,ω^α)^ω\kern{0.17em}0 = 
ω^{ω^{⋰^{ω^0}}}
\\
\varepsilon_{α^+} &= (λα,ω^α)^ω\kern{0.17em}({ε_α}^+) = 
ω^{ω^{⋰^{ω^{({ε_α}^+)}}}}
\\
\varepsilon_{\text{lim}\kern{0.17em}f} &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\varepsilon_{f\kern{0.17em}n} = \text{lim}(ε_{f\kern{0.17em}0},ε_{f\kern{0.17em}1},...)
\end{aligned}
$$

<pre class="Agda"><a id="ε-0"></a><a id="14831" href="Veblen.Basic.html#14831" class="Function">ε-0</a> <a id="14835" class="Symbol">:</a> <a id="14837" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14839" class="Number">0</a> <a id="14841" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="14843" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="14849" class="Symbol">(</a><a id="14850" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="14852" href="Veblen.Basic.html#11220" class="Function Operator">^_</a><a id="14854" class="Symbol">)</a> <a id="14856" class="Number">0</a>
<a id="14858" href="Veblen.Basic.html#14831" class="Function">ε-0</a> <a id="14862" class="Symbol">=</a> <a id="14864" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="ε-suc"></a><a id="14870" href="Veblen.Basic.html#14870" class="Function">ε-suc</a> <a id="14876" class="Symbol">:</a> <a id="14878" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14880" class="Symbol">(</a><a id="14881" class="InductiveConstructor">suc</a> <a id="14885" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="14886" class="Symbol">)</a> <a id="14888" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="14890" href="Veblen.Basic.html#11593" class="Function">iterω</a> <a id="14896" class="Symbol">(</a><a id="14897" href="Veblen.Basic.html#4667" class="Function">ω</a> <a id="14899" href="Veblen.Basic.html#11220" class="Function Operator">^_</a><a id="14901" class="Symbol">)</a> <a id="14903" class="Symbol">(</a><a id="14904" class="InductiveConstructor">suc</a> <a id="14908" class="Symbol">(</a><a id="14909" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14911" href="Veblen.Basic.html#4200" class="Generalizable">α</a><a id="14912" class="Symbol">))</a>
<a id="14915" href="Veblen.Basic.html#14870" class="Function">ε-suc</a> <a id="14921" class="Symbol">=</a> <a id="14923" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="ε-lim"></a><a id="14929" href="Veblen.Basic.html#14929" class="Function">ε-lim</a> <a id="14935" class="Symbol">:</a> <a id="14937" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14939" class="Symbol">(</a><a id="14940" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="14944" href="Veblen.Basic.html#9473" class="Generalizable">f</a><a id="14945" class="Symbol">)</a> <a id="14947" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="14949" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="14953" class="Symbol">λ</a> <a id="14955" href="Veblen.Basic.html#14955" class="Bound">n</a> <a id="14957" class="Symbol">→</a> <a id="14959" href="Veblen.Basic.html#14392" class="Function">ε</a> <a id="14961" class="Symbol">(</a><a id="14962" href="Veblen.Basic.html#9473" class="Generalizable">f</a> <a id="14964" href="Veblen.Basic.html#14955" class="Bound">n</a><a id="14965" class="Symbol">)</a>
<a id="14967" href="Veblen.Basic.html#14929" class="Function">ε-lim</a> <a id="14973" class="Symbol">=</a> <a id="14975" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定义** $\zeta$ 是 $ε$ 的不动点枚举

$$
ζ := \text{fixpt}\kern{0.17em}ε
$$

<pre class="Agda"><a id="ζ"></a><a id="15061" href="Veblen.Basic.html#15061" class="Function">ζ</a> <a id="15063" class="Symbol">:</a> <a id="15065" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="15069" class="Symbol">→</a> <a id="15071" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="15075" href="Veblen.Basic.html#15061" class="Function">ζ</a> <a id="15077" class="Symbol">=</a> <a id="15079" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="15085" href="Veblen.Basic.html#14392" class="Function">ε</a>
</pre>
**定理** 依定义有

$$
\begin{aligned}
\zeta_0 &= ε^ω\kern{0.17em}0 =
ε_{ε_{⋱_{ε_0}}}
\\
\zeta_{α^+} &= ε^ω\kern{0.17em}({\zeta_α}^+) =
ε_{ε_{⋱_{({\zeta_α}^+)}}}
\\
\zeta_{\text{lim}\kern{0.17em}f} &= \text{lim}\kern{0.17em}λ\kern{0.17em}n\kern{0.17em},\kern{0.17em}\zeta_{f\kern{0.17em}n} = \text{lim}(ζ_{f\kern{0.17em}0},ζ_{f\kern{0.17em}1},...)
\end{aligned}
$$

**定义** $\eta$ 是 $\zeta$ 的不动点枚举

$$
η := \text{fixpt}\kern{0.17em}ζ
$$

<pre class="Agda"><a id="η"></a><a id="15530" href="Veblen.Basic.html#15530" class="Function">η</a> <a id="15532" class="Symbol">:</a> <a id="15534" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="15538" class="Symbol">→</a> <a id="15540" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
<a id="15544" href="Veblen.Basic.html#15530" class="Function">η</a> <a id="15546" class="Symbol">=</a> <a id="15548" href="Veblen.Basic.html#13474" class="Function">fixpt</a> <a id="15554" href="Veblen.Basic.html#15061" class="Function">ζ</a>
</pre>
**例** 一个很大的大数:

$$
\text{oom} := f_{η_0} 99 = f_{
  ζ_{ζ_{⋱_{ζ_0}}}
}99
$$

其中 $ζ_{ζ_{⋱_{ζ_0}}}$ 是从 $ζ_0$ 开始迭代了 99 次 $ζ$.

<pre class="Agda"><a id="oom"></a><a id="15692" href="Veblen.Basic.html#15692" class="Function">oom</a> <a id="15696" class="Symbol">=</a> <a id="15698" href="Veblen.Basic.html#5715" class="Function">FGH.f</a> <a id="15704" class="Symbol">(</a><a id="15705" href="Veblen.Basic.html#15530" class="Function">η</a> <a id="15707" class="Number">0</a><a id="15708" class="Symbol">)</a> <a id="15710" class="Number">99</a>
</pre>