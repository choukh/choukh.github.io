---
title: 形式化大数数学 (1.2 - Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/705436498
---

# 形式化大数数学 (1.2 - Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Multinary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Multinary.lagda.md)  
> 高亮渲染: [Multinary.html](https://choukh.github.io/agda-googology/Veblen.Multinary.html)  

<pre class="Agda"><a id="379" class="Keyword">module</a> <a id="386" href="Veblen.Multinary.html" class="Module">Veblen.Multinary</a> <a id="403" class="Keyword">where</a>
<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="Veblen.Basic.html" class="Module">Veblen.Basic</a> <a id="434" class="Keyword">public</a>
</pre>
## 综述

前篇讲了Veblen层级的构造需要的三个高阶函数

1. 无穷迭代 $λF,F^\omega$
2. 跳出运算 $\text{jump}$
3. 不动点的枚举 $\text{fixpt}$

以及 $\varepsilon, \zeta, \eta$ 函数的定义

$$
\begin{aligned}
ε &:= \text{fixpt}\kern{0.17em}λα,ω\kern{0.17em}^α \\
ζ &:= \text{fixpt}\kern{0.17em}ε \\
η &:= \text{fixpt}\kern{0.17em}ζ
\end{aligned}
$$

观察这些定义的形式, 不难发现, 很自然地, 构造更大序数的下一步操作是迭代高阶函数 $\text{fixpt}$ 本身. 这要求一个更高阶的函数 $Φ_2$, 然后我们会想要再次迭代这个更高阶的函数, 这又要求一个更更高阶的函数 $Φ_3$, 乃至 $Φ_4$, 以此类推.

- $Φ_2:(\text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_3:(\text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- $Φ_4:(\text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}) → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- ...

回想梦的开始 $λα,ω\kern{0.17em}^α : \text{Ord} → \text{Ord}$, 把它记作 $\varphi_1$.

- 从 $\varphi_1$ 开始, 用 $Φ_2$ 迭代 $\text{fixpt}$, 得到的函数叫做二元Veblen函数 $\varphi_2 : \text{Ord} → \text{Ord} → \text{Ord}$
- 从 $\varphi_2$ 开始, 用 $Φ_3$ 迭代 $Φ_2$, 得到的函数叫做三元Veblen函数 $\varphi_3 : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- 从 $\varphi_3$ 开始, 用 $Φ_4$ 迭代 $Φ_3$, 得到的函数叫做四元Veblen函数 $\varphi_4 : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$
- ...

$\varphi_1, \varphi_2, ...$ 分别具有定义

- $\varphi_1 := λα,ω\kern{0.17em}^α$
- $\varphi_2 := Φ_2\kern{0.17em}\varphi_1$
- $\varphi_3 := Φ_3\kern{0.17em}\varphi_2$
- $\varphi_4 := Φ_4\kern{0.17em}\varphi_3$
- ...

剩下的只需要处理 $Φ_2, Φ_3, ...$ 的细节.

下标位是稀缺资源. 后文中, 在没有歧义的情况下, 我们会省去表示元数的下标. 如有歧义, 我们用 $\text{Bin}.Φ, \text{Tri}.Φ, \text{Qua}.Φ,...$ 以及 $\text{Bin}.\varphi, \text{Tri}.\varphi, \text{Qua}.\varphi,...$ 来区分元数. 下文中的下标将另作他用, 注意区分.

## 二元Veblen函数

<pre class="Agda"><a id="2096" class="Keyword">module</a> <a id="BinaryVeblen"></a><a id="2103" href="Veblen.Multinary.html#2103" class="Module">BinaryVeblen</a> <a id="2116" class="Keyword">where</a>
</pre>
由上面的讨论, 二元版本的 $Φ$ 需要迭代 $\text{fixpt}$, 这也是由强大的 $\text{rec}$ 函数完成的. 注意 $\text{rec}$ 可以处理任意类型 $A$, 一个序数函数类型不管再高阶, 它也是一个类型, 所以适用 $\text{rec}$. 这是类型论语言的方便之处.

**定义** 二元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord}$, 使用 $\text{rec}$, 其三个参数分别如下.

- 初始值: $F$
- 后继步骤: 迭代 $\text{fixpt}$
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作

即

$$
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}\text{fixpt}\kern{0.17em}(λφ,\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]\kern{0.17em}β)
$$

<pre class="Agda">  <a id="BinaryVeblen.Φ"></a><a id="2618" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="2620" class="Symbol">:</a> <a id="2622" class="Symbol">(</a><a id="2623" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="2627" class="Symbol">→</a> <a id="2629" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="2632" class="Symbol">)</a> <a id="2634" class="Symbol">→</a> <a id="2636" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="2640" class="Symbol">→</a> <a id="2642" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="2646" class="Symbol">→</a> <a id="2648" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="2654" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="2656" href="Veblen.Multinary.html#2656" class="Bound">F</a> <a id="2658" class="Symbol">=</a> <a id="2660" href="Veblen.Basic.html#8977" class="Function">rec</a> <a id="2664" href="Veblen.Multinary.html#2656" class="Bound">F</a> <a id="2666" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="2672" class="Symbol">(λ</a> <a id="2675" href="Veblen.Multinary.html#2675" class="Bound Operator">φ[_]</a> <a id="2680" class="Symbol">→</a> <a id="2682" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="2687" class="Symbol">λ</a> <a id="2689" href="Veblen.Multinary.html#2689" class="Bound">β</a> <a id="2691" class="Symbol">→</a> <a id="2693" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="2697" class="Symbol">λ</a> <a id="2699" href="Veblen.Multinary.html#2699" class="Bound">n</a> <a id="2701" class="Symbol">→</a> <a id="2703" href="Veblen.Multinary.html#2675" class="Bound Operator">φ[</a> <a id="2706" href="Veblen.Multinary.html#2699" class="Bound">n</a> <a id="2708" href="Veblen.Multinary.html#2675" class="Bound Operator">]</a> <a id="2710" href="Veblen.Multinary.html#2689" class="Bound">β</a><a id="2711" class="Symbol">)</a>
</pre>
**注意** 极限步的跳出操作是反直觉的一步. 从通常的定义式反推不难发现这里需要跳出. 仔细分析二元Veblen函数的序性质才能更好的理解这里跳出的动机, 具体可以参看[Agda大序数(9) 二元Veblen函数](https://zhuanlan.zhihu.com/p/585882648). 这里只需简单的理解为是为了更好的性质和更高的增长率就行了.

**定义** 二元Veblen函数

$$\varphi := Φ\kern{0.17em}λα,ω\kern{0.17em}^α$$

<pre class="Agda">  <a id="BinaryVeblen.φ"></a><a id="2978" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="2980" class="Symbol">:</a> <a id="2982" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="2986" class="Symbol">→</a> <a id="2988" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="2992" class="Symbol">→</a> <a id="2994" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="3000" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3002" class="Symbol">=</a> <a id="3004" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="3006" class="Symbol">(</a><a id="3007" href="Veblen.Basic.html#4641" class="Function">ω</a> <a id="3009" href="Veblen.Basic.html#11194" class="Function Operator">^_</a><a id="3011" class="Symbol">)</a>
</pre>
我们习惯将最后一个参数之前的所有参数都写成下标.

**例** 由定义, 以下等式成立.

$$
\begin{aligned}
\varphi_0 &= λα,ω\kern{0.17em}^α \\
\varphi_1 &= ε \\
\varphi_2 &= ζ \\
\varphi_3 &= η
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ-0"></a><a id="3198" href="Veblen.Multinary.html#3198" class="Function">φ-0</a> <a id="3202" class="Symbol">:</a> <a id="3204" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3206" class="Number">0</a> <a id="3208" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3210" href="Veblen.Basic.html#4641" class="Function">ω</a> <a id="3212" href="Veblen.Basic.html#11194" class="Function Operator">^_</a>
  <a id="3217" href="Veblen.Multinary.html#3198" class="Function">φ-0</a> <a id="3221" class="Symbol">=</a> <a id="3223" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-1"></a><a id="3231" href="Veblen.Multinary.html#3231" class="Function">φ-1</a> <a id="3235" class="Symbol">:</a> <a id="3237" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3239" class="Number">1</a> <a id="3241" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3243" href="Veblen.Basic.html#14282" class="Function">ε</a>
  <a id="3247" href="Veblen.Multinary.html#3231" class="Function">φ-1</a> <a id="3251" class="Symbol">=</a> <a id="3253" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-2"></a><a id="3261" href="Veblen.Multinary.html#3261" class="Function">φ-2</a> <a id="3265" class="Symbol">:</a> <a id="3267" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3269" class="Number">2</a> <a id="3271" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3273" href="Veblen.Basic.html#14951" class="Function">ζ</a>
  <a id="3277" href="Veblen.Multinary.html#3261" class="Function">φ-2</a> <a id="3281" class="Symbol">=</a> <a id="3283" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-3"></a><a id="3291" href="Veblen.Multinary.html#3291" class="Function">φ-3</a> <a id="3295" class="Symbol">:</a> <a id="3297" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3299" class="Number">3</a> <a id="3301" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3303" href="Veblen.Basic.html#15420" class="Function">η</a>
  <a id="3307" href="Veblen.Multinary.html#3291" class="Function">φ-3</a> <a id="3311" class="Symbol">=</a> <a id="3313" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+} &= \text{fixpt}\kern{0.17em}φ_α \\
\varphi_{\text{lim}\kern{0.17em}f} &= \text{jump}\kern{0.17em}λα,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}α
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ-suc"></a><a id="3584" href="Veblen.Multinary.html#3584" class="Function">φ-suc</a> <a id="3590" class="Symbol">:</a> <a id="3592" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3594" class="Symbol">(</a><a id="3595" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="3599" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="3600" class="Symbol">)</a> <a id="3602" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3604" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="3610" class="Symbol">(</a><a id="3611" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3613" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="3614" class="Symbol">)</a>
  <a id="3618" href="Veblen.Multinary.html#3584" class="Function">φ-suc</a> <a id="3624" class="Symbol">=</a> <a id="3626" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim"></a><a id="3634" href="Veblen.Multinary.html#3634" class="Function">φ-lim</a> <a id="3640" class="Symbol">:</a> <a id="3642" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3644" class="Symbol">(</a><a id="3645" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="3649" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="3650" class="Symbol">)</a> <a id="3652" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3654" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="3659" class="Symbol">λ</a> <a id="3661" href="Veblen.Multinary.html#3661" class="Bound">α</a> <a id="3663" class="Symbol">→</a> <a id="3665" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="3669" class="Symbol">λ</a> <a id="3671" href="Veblen.Multinary.html#3671" class="Bound">n</a> <a id="3673" class="Symbol">→</a> <a id="3675" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3677" class="Symbol">(</a><a id="3678" href="Veblen.Basic.html#9447" class="Generalizable">f</a> <a id="3680" href="Veblen.Multinary.html#3671" class="Bound">n</a><a id="3681" class="Symbol">)</a> <a id="3683" href="Veblen.Multinary.html#3661" class="Bound">α</a>
  <a id="3687" href="Veblen.Multinary.html#3634" class="Function">φ-lim</a> <a id="3693" class="Symbol">=</a> <a id="3695" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
为了对 $\text{jump}$ 的行为有更加直观的感受, 对第一个参数为极限的情况, 我们对第二个参数再次分成零, 后继和极限的情况进行讨论, 有如下等式成立.

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}0 &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(β^+) &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}(\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}β)^+ \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(\text{lim}\kern{0.17em}g) &= \text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f}\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ-lim-0"></a><a id="4283" href="Veblen.Multinary.html#4283" class="Function">φ-lim-0</a> <a id="4291" class="Symbol">:</a> <a id="4293" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4295" class="Symbol">(</a><a id="4296" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4300" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="4301" class="Symbol">)</a> <a id="4303" class="Number">0</a> <a id="4305" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4307" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4311" class="Symbol">λ</a> <a id="4313" href="Veblen.Multinary.html#4313" class="Bound">n</a> <a id="4315" class="Symbol">→</a> <a id="4317" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4319" class="Symbol">(</a><a id="4320" href="Veblen.Basic.html#9447" class="Generalizable">f</a> <a id="4322" href="Veblen.Multinary.html#4313" class="Bound">n</a><a id="4323" class="Symbol">)</a> <a id="4325" class="Number">0</a>
  <a id="4329" href="Veblen.Multinary.html#4283" class="Function">φ-lim-0</a> <a id="4337" class="Symbol">=</a> <a id="4339" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim-suc"></a><a id="4347" href="Veblen.Multinary.html#4347" class="Function">φ-lim-suc</a> <a id="4357" class="Symbol">:</a> <a id="4359" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4361" class="Symbol">(</a><a id="4362" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4366" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="4367" class="Symbol">)</a> <a id="4369" class="Symbol">(</a><a id="4370" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="4374" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="4375" class="Symbol">)</a> <a id="4377" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4379" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4383" class="Symbol">λ</a> <a id="4385" href="Veblen.Multinary.html#4385" class="Bound">n</a> <a id="4387" class="Symbol">→</a> <a id="4389" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4391" class="Symbol">(</a><a id="4392" href="Veblen.Basic.html#9447" class="Generalizable">f</a> <a id="4394" href="Veblen.Multinary.html#4385" class="Bound">n</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">(</a><a id="4398" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="4402" class="Symbol">(</a><a id="4403" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4405" class="Symbol">(</a><a id="4406" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4410" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="4411" class="Symbol">)</a> <a id="4413" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="4414" class="Symbol">))</a>
  <a id="4419" href="Veblen.Multinary.html#4347" class="Function">φ-lim-suc</a> <a id="4429" class="Symbol">=</a> <a id="4431" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim-lim"></a><a id="4439" href="Veblen.Multinary.html#4439" class="Function">φ-lim-lim</a> <a id="4449" class="Symbol">:</a> <a id="4451" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4453" class="Symbol">(</a><a id="4454" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4458" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="4459" class="Symbol">)</a> <a id="4461" class="Symbol">(</a><a id="4462" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4466" href="Veblen.Basic.html#9449" class="Generalizable">g</a><a id="4467" class="Symbol">)</a> <a id="4469" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4471" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4475" class="Symbol">λ</a> <a id="4477" href="Veblen.Multinary.html#4477" class="Bound">n</a> <a id="4479" class="Symbol">→</a> <a id="4481" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4483" class="Symbol">(</a><a id="4484" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="4488" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="4489" class="Symbol">)</a> <a id="4491" class="Symbol">(</a><a id="4492" href="Veblen.Basic.html#9449" class="Generalizable">g</a> <a id="4494" href="Veblen.Multinary.html#4477" class="Bound">n</a><a id="4495" class="Symbol">)</a>
  <a id="4499" href="Veblen.Multinary.html#4439" class="Function">φ-lim-lim</a> <a id="4509" class="Symbol">=</a> <a id="4511" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
很快, 我们来到了二元Veblen函数的能力极限.

**定义** 对函数 $λα,φ_α\kern{0.17em}0$ 取不动点枚举, 得到的函数称为 $\Gamma$.

$$
\Gamma := \text{fixpt}\kern{0.17em}λα,φ_α\kern{0.17em}0
$$

<pre class="Agda">  <a id="BinaryVeblen.Γ"></a><a id="4682" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4684" class="Symbol">:</a> <a id="4686" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="4690" class="Symbol">→</a> <a id="4692" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="4698" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4700" class="Symbol">=</a> <a id="4702" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="4708" class="Symbol">λ</a> <a id="4710" href="Veblen.Multinary.html#4710" class="Bound">α</a> <a id="4712" class="Symbol">→</a> <a id="4714" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4716" href="Veblen.Multinary.html#4710" class="Bound">α</a> <a id="4718" class="Number">0</a>
</pre>
**例** 最小的 $\Gamma$ 数是

$$Γ_0 = φ_{φ_{φ_{φ_{...}0}\kern{0.17em}0}\kern{0.17em}0}\kern{0.17em}0$$

<pre class="Agda">  <a id="BinaryVeblen.Γ-0"></a><a id="4832" href="Veblen.Multinary.html#4832" class="Function">Γ-0</a> <a id="4836" class="Symbol">:</a> <a id="4838" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4840" class="Number">0</a> <a id="4842" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4844" href="Veblen.Basic.html#11483" class="Function">iterω</a> <a id="4850" class="Symbol">(λ</a> <a id="4853" href="Veblen.Multinary.html#4853" class="Bound">α</a> <a id="4855" class="Symbol">→</a> <a id="4857" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4859" href="Veblen.Multinary.html#4853" class="Bound">α</a> <a id="4861" class="Number">0</a><a id="4862" class="Symbol">)</a> <a id="4864" class="Number">0</a>
  <a id="4868" href="Veblen.Multinary.html#4832" class="Function">Γ-0</a> <a id="4872" class="Symbol">=</a> <a id="4874" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
没有什么能阻止我们继续取不动点枚举. 将 $\Gamma$ 看作新的 $λα,ω\kern{0.17em}^α$, 我们可以得到所谓第二代 $\varepsilon, \zeta, \eta$ 函数, 分别记作 $\dot{\varepsilon}, \dot{\zeta}, \dot{\eta}$.

$$
\begin{aligned}
\dot{\varepsilon} &:= \text{fixpt}\kern{0.17em}Γ \\
\dot{\zeta} &:= \text{fixpt}\kern{0.17em}\dot{\varepsilon} \\
\dot{\eta} &:= \text{fixpt}\kern{0.17em}\dot{\zeta}
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.ε̇"></a><a id="5250" href="Veblen.Multinary.html#5250" class="Function">ε̇</a> <a id="BinaryVeblen.ζ̇"></a><a id="5253" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a> <a id="BinaryVeblen.η̇"></a><a id="5256" href="Veblen.Multinary.html#5256" class="Function">η̇</a> <a id="5259" class="Symbol">:</a> <a id="5261" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5265" class="Symbol">→</a> <a id="5267" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="5273" href="Veblen.Multinary.html#5250" class="Function">ε̇</a> <a id="5276" class="Symbol">=</a> <a id="5278" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5284" href="Veblen.Multinary.html#4682" class="Function">Γ</a>
  <a id="5288" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a> <a id="5291" class="Symbol">=</a> <a id="5293" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5299" href="Veblen.Multinary.html#5250" class="Function">ε̇</a>
  <a id="5304" href="Veblen.Multinary.html#5256" class="Function">η̇</a> <a id="5307" class="Symbol">=</a> <a id="5309" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5315" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a>
</pre>
然后有第二代 $\varphi$ 和第二代 $\Gamma$ 函数.

$$
\begin{aligned}
\dot{\varphi} &:= Φ\kern{0.17em}Γ \\
\dot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\dot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ̇"></a><a id="5518" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5521" class="Symbol">:</a> <a id="5523" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5527" class="Symbol">→</a> <a id="5529" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5533" class="Symbol">→</a> <a id="5535" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="5541" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5544" class="Symbol">=</a> <a id="5546" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="5548" href="Veblen.Multinary.html#4682" class="Function">Γ</a>

  <a id="BinaryVeblen.Γ̇"></a><a id="5553" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a> <a id="5556" class="Symbol">:</a> <a id="5558" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5562" class="Symbol">→</a> <a id="5564" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="5570" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a> <a id="5573" class="Symbol">=</a> <a id="5575" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5581" class="Symbol">λ</a> <a id="5583" href="Veblen.Multinary.html#5583" class="Bound">α</a> <a id="5585" class="Symbol">→</a> <a id="5587" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5590" href="Veblen.Multinary.html#5583" class="Bound">α</a> <a id="5592" class="Number">0</a>
</pre>
乃至第三代 $\varepsilon, \zeta, \eta$ 函数

$$
\begin{aligned}
\ddot{\varepsilon} &:= \text{fixpt}\kern{0.17em}\dot{\Gamma} \\
\ddot{\zeta} &:= \text{fixpt}\kern{0.17em}\ddot{\varepsilon} \\
\ddot{\eta} &:= \text{fixpt}\kern{0.17em}\ddot{\zeta}
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.ε̈"></a><a id="5865" href="Veblen.Multinary.html#5865" class="Function">ε̈</a> <a id="BinaryVeblen.ζ̈"></a><a id="5868" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a> <a id="BinaryVeblen.η̈"></a><a id="5871" href="Veblen.Multinary.html#5871" class="Function">η̈</a> <a id="5874" class="Symbol">:</a> <a id="5876" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="5880" class="Symbol">→</a> <a id="5882" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="5888" href="Veblen.Multinary.html#5865" class="Function">ε̈</a> <a id="5891" class="Symbol">=</a> <a id="5893" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5899" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>
  <a id="5904" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a> <a id="5907" class="Symbol">=</a> <a id="5909" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5915" href="Veblen.Multinary.html#5865" class="Function">ε̈</a>
  <a id="5920" href="Veblen.Multinary.html#5871" class="Function">η̈</a> <a id="5923" class="Symbol">=</a> <a id="5925" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="5931" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a>
</pre>
和第三代 $\varphi$ 和第三代 $\Gamma$ 函数.

$$
\begin{aligned}
\ddot{\varphi} &:= Φ\kern{0.17em}\dot{\Gamma} \\
\ddot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\ddot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ̈"></a><a id="6146" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6149" class="Symbol">:</a> <a id="6151" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="6155" class="Symbol">→</a> <a id="6157" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="6161" class="Symbol">→</a> <a id="6163" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="6169" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6172" class="Symbol">=</a> <a id="6174" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="6176" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>

  <a id="BinaryVeblen.Γ̈"></a><a id="6182" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a> <a id="6185" class="Symbol">:</a> <a id="6187" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="6191" class="Symbol">→</a> <a id="6193" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="6199" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a> <a id="6202" class="Symbol">=</a> <a id="6204" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="6210" class="Symbol">λ</a> <a id="6212" href="Veblen.Multinary.html#6212" class="Bound">α</a> <a id="6214" class="Symbol">→</a> <a id="6216" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6219" href="Veblen.Multinary.html#6212" class="Bound">α</a> <a id="6221" class="Number">0</a>
</pre>
以此类推, 直至超限代. 三元Veblen函数将把这些后代函数囊括其中.

## 三元Veblen函数

<pre class="Agda"><a id="6289" class="Keyword">module</a> <a id="TrinaryVeblen"></a><a id="6296" href="Veblen.Multinary.html#6296" class="Module">TrinaryVeblen</a> <a id="6310" class="Keyword">where</a>
</pre>
本小节我们将上一小节的谈论过事物 $x$ 记作 $\text{Bin}.x$, 以让出命名空间, 但没有歧义时会省略.

<pre class="Agda">  <a id="6392" class="Keyword">private</a> <a id="6400" class="Keyword">module</a> <a id="TrinaryVeblen.Bin"></a><a id="6407" href="Veblen.Multinary.html#6407" class="Module">Bin</a> <a id="6411" class="Symbol">=</a> <a id="6413" href="Veblen.Multinary.html#2103" class="Module">BinaryVeblen</a>
  <a id="6428" class="Keyword">open</a> <a id="6433" href="Veblen.Multinary.html#6407" class="Module">Bin</a> <a id="6437" class="Keyword">using</a> <a id="6443" class="Symbol">(</a><a id="6444" href="Veblen.Multinary.html#4682" class="Function">Γ</a><a id="6445" class="Symbol">;</a> <a id="6447" href="Veblen.Multinary.html#5250" class="Function">ε̇</a><a id="6449" class="Symbol">;</a> <a id="6451" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a><a id="6453" class="Symbol">;</a> <a id="6455" href="Veblen.Multinary.html#5256" class="Function">η̇</a><a id="6457" class="Symbol">;</a> <a id="6459" href="Veblen.Multinary.html#5518" class="Function">φ̇</a><a id="6461" class="Symbol">;</a> <a id="6463" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a><a id="6465" class="Symbol">;</a> <a id="6467" href="Veblen.Multinary.html#5865" class="Function">ε̈</a><a id="6469" class="Symbol">;</a> <a id="6471" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a><a id="6473" class="Symbol">;</a> <a id="6475" href="Veblen.Multinary.html#5871" class="Function">η̈</a><a id="6477" class="Symbol">;</a> <a id="6479" href="Veblen.Multinary.html#6146" class="Function">φ̈</a><a id="6481" class="Symbol">;</a> <a id="6483" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a><a id="6485" class="Symbol">)</a>
</pre>
**定义** 三元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord} → \text{Ord}$, 使用 $\text{rec}$, 其三个参数分别如下.

- 初始值: $F$
- 后继步骤: 迭代 $λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)$
  - 一些解释
    - 此处迭代的是二元函数 $\text{Ord} → \text{Ord} → \text{Ord}$, 以得到一个三元函数.
    - 参数 $φ_α$ 是上一步的结果, 它是一个二元函数, 看作是对三元函数 $φ$ 输入了上一步的编号 $α$ 所得到的结果.
    - 这一步我们先对 $λβ,φ_{α,β}\kern{0.17em}0$ 取不动点枚举, 再交给二元 $Φ$ 处理
      - 回想上一小节我们是怎么从一代 $φ$ 得到二代 $φ$ 的, 这里的处理方式就是对该操作的反映.
  - 注意: 对任意元 $φ$, 我们都是取第二个参数的不动点枚举, 而对右边剩下的参数全部填零. 二元 $Φ$ 的时候这个规律还看不出来, 现在才显现出来.
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作, 再交给二元 $Φ$ 处理
  - 注意: 与后继步骤类似地, 这里是对第二个参数跳出, 右边其余参数全部填零.

即

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)) \\
&(λφ,\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_β\kern{0.17em}0))
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.Φ"></a><a id="7436" href="Veblen.Multinary.html#7436" class="Function">Φ</a> <a id="7438" class="Symbol">:</a> <a id="7440" class="Symbol">(</a><a id="7441" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7445" class="Symbol">→</a> <a id="7447" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7451" class="Symbol">→</a> <a id="7453" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="7456" class="Symbol">)</a> <a id="7458" class="Symbol">→</a> <a id="7460" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7464" class="Symbol">→</a> <a id="7466" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7470" class="Symbol">→</a> <a id="7472" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7476" class="Symbol">→</a> <a id="7478" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="7484" href="Veblen.Multinary.html#7436" class="Function">Φ</a> <a id="7486" href="Veblen.Multinary.html#7486" class="Bound">F</a> <a id="7488" class="Symbol">=</a> <a id="7490" href="Veblen.Basic.html#8977" class="Function">rec</a> <a id="7494" href="Veblen.Multinary.html#7486" class="Bound">F</a>
    <a id="7500" class="Symbol">(λ</a> <a id="7503" href="Veblen.Multinary.html#7503" class="Bound">φ-α</a>  <a id="7508" class="Symbol">→</a> <a id="7510" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="7516" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="7518" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="7524" class="Symbol">λ</a> <a id="7526" href="Veblen.Multinary.html#7526" class="Bound">β</a> <a id="7528" class="Symbol">→</a> <a id="7530" href="Veblen.Multinary.html#7503" class="Bound">φ-α</a> <a id="7534" href="Veblen.Multinary.html#7526" class="Bound">β</a> <a id="7536" class="Number">0</a><a id="7537" class="Symbol">)</a>
    <a id="7543" class="Symbol">(λ</a> <a id="7546" href="Veblen.Multinary.html#7546" class="Bound Operator">φ[_]</a> <a id="7551" class="Symbol">→</a> <a id="7553" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="7559" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="7561" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="7566" class="Symbol">λ</a> <a id="7568" href="Veblen.Multinary.html#7568" class="Bound">β</a> <a id="7570" class="Symbol">→</a> <a id="7572" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="7576" class="Symbol">λ</a> <a id="7578" href="Veblen.Multinary.html#7578" class="Bound">n</a> <a id="7580" class="Symbol">→</a> <a id="7582" href="Veblen.Multinary.html#7546" class="Bound Operator">φ[</a> <a id="7585" href="Veblen.Multinary.html#7578" class="Bound">n</a> <a id="7587" href="Veblen.Multinary.html#7546" class="Bound Operator">]</a> <a id="7589" href="Veblen.Multinary.html#7568" class="Bound">β</a> <a id="7591" class="Number">0</a><a id="7592" class="Symbol">)</a>
</pre>
**定义** 三元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Bin}.\varphi$$

<pre class="Agda">  <a id="TrinaryVeblen.φ"></a><a id="7677" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="7679" class="Symbol">:</a> <a id="7681" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7685" class="Symbol">→</a> <a id="7687" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7691" class="Symbol">→</a> <a id="7693" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="7697" class="Symbol">→</a> <a id="7699" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="7705" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="7707" class="Symbol">=</a> <a id="7709" href="Veblen.Multinary.html#7436" class="Function">Φ</a> <a id="7711" href="Veblen.Multinary.html#2978" class="Function">Bin.φ</a>
</pre>
**例** 由定义, 以下等式成立.

$$
\begin{aligned}
\varphi_0 &= \text{Bin}.\varphi \\
\varphi_{1,0} &= \Gamma \\
\varphi_{1,1} &= \dot{\varepsilon} \\
\varphi_{1,2} &= \dot{\zeta} \\
\varphi_{1,3} &= \dot{\eta} \\
\varphi_{1} &= \dot{\varphi} \\
\varphi_{2,0} &= \dot{\Gamma} \\
\varphi_{2,1} &= \ddot{\varepsilon} \\
\varphi_{2,2} &= \ddot{\zeta} \\
\varphi_{2,3} &= \ddot{\eta} \\
\varphi_{2} &= \ddot{\varphi} \\
\varphi_{3,0} &= \ddot{\Gamma} \\
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.φ-0"></a><a id="8188" href="Veblen.Multinary.html#8188" class="Function">φ-0</a> <a id="8192" class="Symbol">:</a> <a id="8194" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8196" class="Number">0</a> <a id="8198" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8200" href="Veblen.Multinary.html#2978" class="Function">Bin.φ</a>
  <a id="8208" href="Veblen.Multinary.html#8188" class="Function">φ-0</a> <a id="8212" class="Symbol">=</a> <a id="8214" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-0"></a><a id="8222" href="Veblen.Multinary.html#8222" class="Function">φ-1-0</a> <a id="8228" class="Symbol">:</a> <a id="8230" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8232" class="Number">1</a> <a id="8234" class="Number">0</a> <a id="8236" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8238" href="Veblen.Multinary.html#4682" class="Function">Γ</a>
  <a id="8242" href="Veblen.Multinary.html#8222" class="Function">φ-1-0</a> <a id="8248" class="Symbol">=</a> <a id="8250" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-1"></a><a id="8258" href="Veblen.Multinary.html#8258" class="Function">φ-1-1</a> <a id="8264" class="Symbol">:</a> <a id="8266" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8268" class="Number">1</a> <a id="8270" class="Number">1</a> <a id="8272" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8274" href="Veblen.Multinary.html#5250" class="Function">ε̇</a>
  <a id="8279" href="Veblen.Multinary.html#8258" class="Function">φ-1-1</a> <a id="8285" class="Symbol">=</a> <a id="8287" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-2"></a><a id="8295" href="Veblen.Multinary.html#8295" class="Function">φ-1-2</a> <a id="8301" class="Symbol">:</a> <a id="8303" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8305" class="Number">1</a> <a id="8307" class="Number">2</a> <a id="8309" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8311" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a>
  <a id="8316" href="Veblen.Multinary.html#8295" class="Function">φ-1-2</a> <a id="8322" class="Symbol">=</a> <a id="8324" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-3"></a><a id="8332" href="Veblen.Multinary.html#8332" class="Function">φ-1-3</a> <a id="8338" class="Symbol">:</a> <a id="8340" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8342" class="Number">1</a> <a id="8344" class="Number">3</a> <a id="8346" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8348" href="Veblen.Multinary.html#5256" class="Function">η̇</a>
  <a id="8353" href="Veblen.Multinary.html#8332" class="Function">φ-1-3</a> <a id="8359" class="Symbol">=</a> <a id="8361" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1"></a><a id="8369" href="Veblen.Multinary.html#8369" class="Function">φ-1</a> <a id="8373" class="Symbol">:</a> <a id="8375" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8377" class="Number">1</a> <a id="8379" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8381" href="Veblen.Multinary.html#5518" class="Function">φ̇</a>
  <a id="8386" href="Veblen.Multinary.html#8369" class="Function">φ-1</a> <a id="8390" class="Symbol">=</a> <a id="8392" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-0"></a><a id="8400" href="Veblen.Multinary.html#8400" class="Function">φ-2-0</a> <a id="8406" class="Symbol">:</a> <a id="8408" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8410" class="Number">2</a> <a id="8412" class="Number">0</a> <a id="8414" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8416" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>
  <a id="8421" href="Veblen.Multinary.html#8400" class="Function">φ-2-0</a> <a id="8427" class="Symbol">=</a> <a id="8429" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-1"></a><a id="8437" href="Veblen.Multinary.html#8437" class="Function">φ-2-1</a> <a id="8443" class="Symbol">:</a> <a id="8445" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8447" class="Number">2</a> <a id="8449" class="Number">1</a> <a id="8451" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8453" href="Veblen.Multinary.html#5865" class="Function">ε̈</a>
  <a id="8458" href="Veblen.Multinary.html#8437" class="Function">φ-2-1</a> <a id="8464" class="Symbol">=</a> <a id="8466" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-2"></a><a id="8474" href="Veblen.Multinary.html#8474" class="Function">φ-2-2</a> <a id="8480" class="Symbol">:</a> <a id="8482" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8484" class="Number">2</a> <a id="8486" class="Number">2</a> <a id="8488" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8490" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a>
  <a id="8495" href="Veblen.Multinary.html#8474" class="Function">φ-2-2</a> <a id="8501" class="Symbol">=</a> <a id="8503" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-3"></a><a id="8511" href="Veblen.Multinary.html#8511" class="Function">φ-2-3</a> <a id="8517" class="Symbol">:</a> <a id="8519" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8521" class="Number">2</a> <a id="8523" class="Number">3</a> <a id="8525" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8527" href="Veblen.Multinary.html#5871" class="Function">η̈</a>
  <a id="8532" href="Veblen.Multinary.html#8511" class="Function">φ-2-3</a> <a id="8538" class="Symbol">=</a> <a id="8540" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2"></a><a id="8548" href="Veblen.Multinary.html#8548" class="Function">φ-2</a> <a id="8552" class="Symbol">:</a> <a id="8554" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8556" class="Number">2</a> <a id="8558" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8560" href="Veblen.Multinary.html#6146" class="Function">φ̈</a>
  <a id="8565" href="Veblen.Multinary.html#8548" class="Function">φ-2</a> <a id="8569" class="Symbol">=</a> <a id="8571" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-3-0"></a><a id="8579" href="Veblen.Multinary.html#8579" class="Function">φ-3-0</a> <a id="8585" class="Symbol">:</a> <a id="8587" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8589" class="Number">3</a> <a id="8591" class="Number">0</a> <a id="8593" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8595" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a>
  <a id="8600" href="Veblen.Multinary.html#8579" class="Function">φ-3-0</a> <a id="8606" class="Symbol">=</a> <a id="8608" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为后继的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0} &= \text{fixpt}λβ,φ_{α,β}\kern{0.17em}0 \\
\varphi_{α^+,β^+} &= \text{fixpt}\kern{0.17em}φ_{α^+,β} \\
\varphi_{α^+,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α^+,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.φ-suc-0"></a><a id="8968" href="Veblen.Multinary.html#8968" class="Function">φ-suc-0</a> <a id="8976" class="Symbol">:</a> <a id="8978" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="8980" class="Symbol">(</a><a id="8981" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="8985" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="8986" class="Symbol">)</a> <a id="8988" class="Number">0</a> <a id="8990" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8992" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="8998" class="Symbol">λ</a> <a id="9000" href="Veblen.Multinary.html#9000" class="Bound">β</a> <a id="9002" class="Symbol">→</a> <a id="9004" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9006" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="9008" href="Veblen.Multinary.html#9000" class="Bound">β</a> <a id="9010" class="Number">0</a>
  <a id="9014" href="Veblen.Multinary.html#8968" class="Function">φ-suc-0</a> <a id="9022" class="Symbol">=</a> <a id="9024" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-suc-suc"></a><a id="9032" href="Veblen.Multinary.html#9032" class="Function">φ-suc-suc</a> <a id="9042" class="Symbol">:</a> <a id="9044" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9046" class="Symbol">(</a><a id="9047" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9051" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="9052" class="Symbol">)</a> <a id="9054" class="Symbol">(</a><a id="9055" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9059" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="9060" class="Symbol">)</a> <a id="9062" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9064" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="9070" class="Symbol">(</a><a id="9071" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9073" class="Symbol">(</a><a id="9074" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9078" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="9079" class="Symbol">)</a> <a id="9081" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="9082" class="Symbol">)</a>
  <a id="9086" href="Veblen.Multinary.html#9032" class="Function">φ-suc-suc</a> <a id="9096" class="Symbol">=</a> <a id="9098" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-suc-lim"></a><a id="9106" href="Veblen.Multinary.html#9106" class="Function">φ-suc-lim</a> <a id="9116" class="Symbol">:</a> <a id="9118" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9120" class="Symbol">(</a><a id="9121" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9125" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="9126" class="Symbol">)</a> <a id="9128" class="Symbol">(</a><a id="9129" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9133" href="Veblen.Basic.html#9449" class="Generalizable">g</a><a id="9134" class="Symbol">)</a> <a id="9136" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9138" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="9143" class="Symbol">λ</a> <a id="9145" href="Veblen.Multinary.html#9145" class="Bound">γ</a> <a id="9147" class="Symbol">→</a> <a id="9149" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9153" class="Symbol">λ</a> <a id="9155" href="Veblen.Multinary.html#9155" class="Bound">n</a> <a id="9157" class="Symbol">→</a> <a id="9159" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9161" class="Symbol">(</a><a id="9162" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9166" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="9167" class="Symbol">)</a> <a id="9169" class="Symbol">(</a><a id="9170" href="Veblen.Basic.html#9449" class="Generalizable">g</a> <a id="9172" href="Veblen.Multinary.html#9155" class="Bound">n</a><a id="9173" class="Symbol">)</a> <a id="9175" href="Veblen.Multinary.html#9145" class="Bound">γ</a>
  <a id="9179" href="Veblen.Multinary.html#9106" class="Function">φ-suc-lim</a> <a id="9189" class="Symbol">=</a> <a id="9191" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为极限的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,β^+} &= \text{fixpt}\kern{0.17em}φ_{\text{lim}\kern{0.17em}f,β}\kern{0.17em} \\
\varphi_{\text{lim}\kern{0.17em}f,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.φ-lim-0"></a><a id="9721" href="Veblen.Multinary.html#9721" class="Function">φ-lim-0</a> <a id="9729" class="Symbol">:</a> <a id="9731" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9733" class="Symbol">(</a><a id="9734" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9738" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="9739" class="Symbol">)</a> <a id="9741" class="Number">0</a> <a id="9743" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9745" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="9750" class="Symbol">λ</a> <a id="9752" href="Veblen.Multinary.html#9752" class="Bound">β</a> <a id="9754" class="Symbol">→</a> <a id="9756" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9760" class="Symbol">λ</a> <a id="9762" href="Veblen.Multinary.html#9762" class="Bound">n</a> <a id="9764" class="Symbol">→</a> <a id="9766" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9768" class="Symbol">(</a><a id="9769" href="Veblen.Basic.html#9447" class="Generalizable">f</a> <a id="9771" href="Veblen.Multinary.html#9762" class="Bound">n</a><a id="9772" class="Symbol">)</a> <a id="9774" href="Veblen.Multinary.html#9752" class="Bound">β</a> <a id="9776" class="Number">0</a>
  <a id="9780" href="Veblen.Multinary.html#9721" class="Function">φ-lim-0</a> <a id="9788" class="Symbol">=</a> <a id="9790" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-lim-suc"></a><a id="9798" href="Veblen.Multinary.html#9798" class="Function">φ-lim-suc</a> <a id="9808" class="Symbol">:</a> <a id="9810" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9812" class="Symbol">(</a><a id="9813" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9817" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="9818" class="Symbol">)</a> <a id="9820" class="Symbol">(</a><a id="9821" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="9825" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="9826" class="Symbol">)</a> <a id="9828" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9830" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="9836" class="Symbol">(</a><a id="9837" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9839" class="Symbol">(</a><a id="9840" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9844" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="9845" class="Symbol">)</a> <a id="9847" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="9848" class="Symbol">)</a>
  <a id="9852" href="Veblen.Multinary.html#9798" class="Function">φ-lim-suc</a> <a id="9862" class="Symbol">=</a> <a id="9864" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-lim-lim"></a><a id="9872" href="Veblen.Multinary.html#9872" class="Function">φ-lim-lim</a> <a id="9882" class="Symbol">:</a> <a id="9884" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9886" class="Symbol">(</a><a id="9887" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9891" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="9892" class="Symbol">)</a> <a id="9894" class="Symbol">(</a><a id="9895" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9899" href="Veblen.Basic.html#9449" class="Generalizable">g</a><a id="9900" class="Symbol">)</a> <a id="9902" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9904" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="9909" class="Symbol">λ</a> <a id="9911" href="Veblen.Multinary.html#9911" class="Bound">γ</a> <a id="9913" class="Symbol">→</a> <a id="9915" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9919" class="Symbol">λ</a> <a id="9921" href="Veblen.Multinary.html#9921" class="Bound">n</a> <a id="9923" class="Symbol">→</a> <a id="9925" href="Veblen.Multinary.html#7677" class="Function">φ</a> <a id="9927" class="Symbol">(</a><a id="9928" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="9932" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="9933" class="Symbol">)</a> <a id="9935" class="Symbol">(</a><a id="9936" href="Veblen.Basic.html#9449" class="Generalizable">g</a> <a id="9938" href="Veblen.Multinary.html#9921" class="Bound">n</a><a id="9939" class="Symbol">)</a> <a id="9941" href="Veblen.Multinary.html#9911" class="Bound">γ</a>
  <a id="9945" href="Veblen.Multinary.html#9872" class="Function">φ-lim-lim</a> <a id="9955" class="Symbol">=</a> <a id="9957" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
## 四元Veblen函数

<pre class="Agda"><a id="9990" class="Keyword">module</a> <a id="QuaternaryVeblen"></a><a id="9997" href="Veblen.Multinary.html#9997" class="Module">QuaternaryVeblen</a> <a id="10014" class="Keyword">where</a>
  <a id="10022" class="Keyword">private</a> <a id="10030" class="Keyword">module</a> <a id="QuaternaryVeblen.Bin"></a><a id="10037" href="Veblen.Multinary.html#10037" class="Module">Bin</a> <a id="10041" class="Symbol">=</a> <a id="10043" href="Veblen.Multinary.html#2103" class="Module">BinaryVeblen</a>
  <a id="10058" class="Keyword">private</a> <a id="10066" class="Keyword">module</a> <a id="QuaternaryVeblen.Tri"></a><a id="10073" href="Veblen.Multinary.html#10073" class="Module">Tri</a> <a id="10077" class="Symbol">=</a> <a id="10079" href="Veblen.Multinary.html#6296" class="Module">TrinaryVeblen</a>
</pre>
摸清二元到三元的规律之后, 三元到四元就是按部就班的操作了.

**定义** 四元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$, 使用 $\text{rec}$

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0))) \\
&(λφ,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_{β,0}\kern{0.17em}0)))
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.Φ"></a><a id="10593" href="Veblen.Multinary.html#10593" class="Function">Φ</a> <a id="10595" class="Symbol">:</a> <a id="10597" class="Symbol">(</a><a id="10598" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10602" class="Symbol">→</a> <a id="10604" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10608" class="Symbol">→</a> <a id="10610" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10614" class="Symbol">→</a> <a id="10616" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="10619" class="Symbol">)</a> <a id="10621" class="Symbol">→</a> <a id="10623" class="Symbol">(</a><a id="10624" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10628" class="Symbol">→</a> <a id="10630" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10634" class="Symbol">→</a> <a id="10636" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10640" class="Symbol">→</a> <a id="10642" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10646" class="Symbol">→</a> <a id="10648" href="Veblen.Basic.html#3262" class="Datatype">Ord</a><a id="10651" class="Symbol">)</a>
  <a id="10655" href="Veblen.Multinary.html#10593" class="Function">Φ</a> <a id="10657" href="Veblen.Multinary.html#10657" class="Bound">F</a> <a id="10659" class="Symbol">=</a> <a id="10661" href="Veblen.Basic.html#8977" class="Function">rec</a> <a id="10665" href="Veblen.Multinary.html#10657" class="Bound">F</a>
    <a id="10671" class="Symbol">(λ</a> <a id="10674" href="Veblen.Multinary.html#10674" class="Bound">φ-α</a>  <a id="10679" class="Symbol">→</a> <a id="10681" href="Veblen.Multinary.html#7436" class="Function">Tri.Φ</a> <a id="10687" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10689" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="10695" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10697" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="10703" class="Symbol">λ</a> <a id="10705" href="Veblen.Multinary.html#10705" class="Bound">β</a> <a id="10707" class="Symbol">→</a> <a id="10709" href="Veblen.Multinary.html#10674" class="Bound">φ-α</a> <a id="10713" href="Veblen.Multinary.html#10705" class="Bound">β</a> <a id="10715" class="Number">0</a> <a id="10717" class="Number">0</a><a id="10718" class="Symbol">)</a>
    <a id="10724" class="Symbol">(λ</a> <a id="10727" href="Veblen.Multinary.html#10727" class="Bound Operator">φ[_]</a> <a id="10732" class="Symbol">→</a> <a id="10734" href="Veblen.Multinary.html#7436" class="Function">Tri.Φ</a> <a id="10740" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10742" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="10748" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10750" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="10755" class="Symbol">λ</a> <a id="10757" href="Veblen.Multinary.html#10757" class="Bound">β</a> <a id="10759" class="Symbol">→</a> <a id="10761" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="10765" class="Symbol">λ</a> <a id="10767" href="Veblen.Multinary.html#10767" class="Bound">n</a> <a id="10769" class="Symbol">→</a> <a id="10771" href="Veblen.Multinary.html#10727" class="Bound Operator">φ[</a> <a id="10774" href="Veblen.Multinary.html#10767" class="Bound">n</a> <a id="10776" href="Veblen.Multinary.html#10727" class="Bound Operator">]</a> <a id="10778" href="Veblen.Multinary.html#10757" class="Bound">β</a> <a id="10780" class="Number">0</a> <a id="10782" class="Number">0</a><a id="10783" class="Symbol">)</a>
</pre>
**定义** 四元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Tri}.\varphi$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ"></a><a id="10868" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="10870" class="Symbol">:</a> <a id="10872" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10876" class="Symbol">→</a> <a id="10878" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10882" class="Symbol">→</a> <a id="10884" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10888" class="Symbol">→</a> <a id="10890" href="Veblen.Basic.html#3262" class="Datatype">Ord</a> <a id="10894" class="Symbol">→</a> <a id="10896" href="Veblen.Basic.html#3262" class="Datatype">Ord</a>
  <a id="10902" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="10904" class="Symbol">=</a> <a id="10906" href="Veblen.Multinary.html#10593" class="Function">Φ</a> <a id="10908" href="Veblen.Multinary.html#7677" class="Function">Tri.φ</a>
</pre>
**例** 第一个参数从无效到刚开始生效, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_0 &= \text{Tri}.\varphi \\
\varphi_{1,0,0} &= \text{fixpt}\kern{0.17em}λα,\text{Tri}.\varphi_{α,0}\kern{0.17em}0 \\
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-0"></a><a id="11127" href="Veblen.Multinary.html#11127" class="Function">φ-0</a> <a id="11131" class="Symbol">:</a> <a id="11133" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11135" class="Number">0</a> <a id="11137" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11139" href="Veblen.Multinary.html#7677" class="Function">Tri.φ</a>
  <a id="11147" href="Veblen.Multinary.html#11127" class="Function">φ-0</a> <a id="11151" class="Symbol">=</a> <a id="11153" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-1-0-0"></a><a id="11161" href="Veblen.Multinary.html#11161" class="Function">φ-1-0-0</a> <a id="11169" class="Symbol">:</a> <a id="11171" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11173" class="Number">1</a> <a id="11175" class="Number">0</a> <a id="11177" class="Number">0</a> <a id="11179" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11181" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="11187" class="Symbol">(λ</a> <a id="11190" href="Veblen.Multinary.html#11190" class="Bound">α</a> <a id="11192" class="Symbol">→</a> <a id="11194" href="Veblen.Multinary.html#7677" class="Function">Tri.φ</a> <a id="11200" href="Veblen.Multinary.html#11190" class="Bound">α</a> <a id="11202" class="Number">0</a> <a id="11204" class="Number">0</a><a id="11205" class="Symbol">)</a>
  <a id="11209" href="Veblen.Multinary.html#11161" class="Function">φ-1-0-0</a> <a id="11217" class="Symbol">=</a> <a id="11219" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 中间两个参数为零, 讨论第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0,0} &= \text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,0,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β,0}\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-suc-0-0"></a><a id="11535" href="Veblen.Multinary.html#11535" class="Function">φ-suc-0-0</a> <a id="11545" class="Symbol">:</a> <a id="11547" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11549" class="Symbol">(</a><a id="11550" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="11554" href="Veblen.Basic.html#4174" class="Generalizable">α</a><a id="11555" class="Symbol">)</a> <a id="11557" class="Number">0</a> <a id="11559" class="Number">0</a> <a id="11561" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11563" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="11569" class="Symbol">λ</a> <a id="11571" href="Veblen.Multinary.html#11571" class="Bound">β</a> <a id="11573" class="Symbol">→</a> <a id="11575" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11577" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="11579" href="Veblen.Multinary.html#11571" class="Bound">β</a> <a id="11581" class="Number">0</a> <a id="11583" class="Number">0</a>
  <a id="11587" href="Veblen.Multinary.html#11535" class="Function">φ-suc-0-0</a> <a id="11597" class="Symbol">=</a> <a id="11599" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-lim-0-0"></a><a id="11607" href="Veblen.Multinary.html#11607" class="Function">φ-lim-0-0</a> <a id="11617" class="Symbol">:</a> <a id="11619" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11621" class="Symbol">(</a><a id="11622" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="11626" href="Veblen.Basic.html#9447" class="Generalizable">f</a><a id="11627" class="Symbol">)</a> <a id="11629" class="Number">0</a> <a id="11631" class="Number">0</a> <a id="11633" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11635" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="11640" class="Symbol">λ</a> <a id="11642" href="Veblen.Multinary.html#11642" class="Bound">β</a> <a id="11644" class="Symbol">→</a> <a id="11646" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="11650" class="Symbol">λ</a> <a id="11652" href="Veblen.Multinary.html#11652" class="Bound">n</a> <a id="11654" class="Symbol">→</a> <a id="11656" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="11658" class="Symbol">(</a><a id="11659" href="Veblen.Basic.html#9447" class="Generalizable">f</a> <a id="11661" href="Veblen.Multinary.html#11652" class="Bound">n</a><a id="11662" class="Symbol">)</a> <a id="11664" href="Veblen.Multinary.html#11642" class="Bound">β</a> <a id="11666" class="Number">0</a> <a id="11668" class="Number">0</a>
  <a id="11672" href="Veblen.Multinary.html#11607" class="Function">φ-lim-0-0</a> <a id="11682" class="Symbol">=</a> <a id="11684" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 将 $φ_α$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β^+,0} &= \text{fixpt}\kern{0.17em}λγ,φ_{α,β,γ}\kern{0.17em}0 \\
\varphi_{α,\text{lim}\kern{0.17em}g,0} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α,g\kern{0.17em}n,γ}\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-α-suc-0"></a><a id="11991" href="Veblen.Multinary.html#11991" class="Function">φ-α-suc-0</a> <a id="12001" class="Symbol">:</a> <a id="12003" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12005" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12007" class="Symbol">(</a><a id="12008" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12012" href="Veblen.Basic.html#4176" class="Generalizable">β</a><a id="12013" class="Symbol">)</a> <a id="12015" class="Number">0</a> <a id="12017" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12019" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="12025" class="Symbol">λ</a> <a id="12027" href="Veblen.Multinary.html#12027" class="Bound">γ</a> <a id="12029" class="Symbol">→</a> <a id="12031" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12033" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12035" href="Veblen.Basic.html#4176" class="Generalizable">β</a> <a id="12037" href="Veblen.Multinary.html#12027" class="Bound">γ</a> <a id="12039" class="Number">0</a>
  <a id="12043" href="Veblen.Multinary.html#11991" class="Function">φ-α-suc-0</a> <a id="12053" class="Symbol">{</a><a id="12054" class="Argument">α</a> <a id="12056" class="Symbol">=</a> <a id="12058" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12062" class="Symbol">}</a>  <a id="12065" class="Symbol">=</a> <a id="12067" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12074" href="Veblen.Multinary.html#11991" class="Function">φ-α-suc-0</a> <a id="12084" class="Symbol">{</a><a id="12085" class="Argument">α</a> <a id="12087" class="Symbol">=</a> <a id="12089" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12093" class="Symbol">_}</a> <a id="12096" class="Symbol">=</a> <a id="12098" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12105" href="Veblen.Multinary.html#11991" class="Function">φ-α-suc-0</a> <a id="12115" class="Symbol">{</a><a id="12116" class="Argument">α</a> <a id="12118" class="Symbol">=</a> <a id="12120" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12124" href="Veblen.Multinary.html#12124" class="Bound">f</a><a id="12125" class="Symbol">}</a> <a id="12127" class="Symbol">=</a> <a id="12129" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-α-lim-0"></a><a id="12137" href="Veblen.Multinary.html#12137" class="Function">φ-α-lim-0</a> <a id="12147" class="Symbol">:</a> <a id="12149" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12151" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12153" class="Symbol">(</a><a id="12154" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12158" href="Veblen.Basic.html#9449" class="Generalizable">g</a><a id="12159" class="Symbol">)</a> <a id="12161" class="Number">0</a> <a id="12163" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12165" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="12170" class="Symbol">λ</a> <a id="12172" href="Veblen.Multinary.html#12172" class="Bound">γ</a> <a id="12174" class="Symbol">→</a> <a id="12176" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12180" class="Symbol">λ</a> <a id="12182" href="Veblen.Multinary.html#12182" class="Bound">n</a> <a id="12184" class="Symbol">→</a> <a id="12186" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12188" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12190" class="Symbol">(</a><a id="12191" href="Veblen.Basic.html#9449" class="Generalizable">g</a> <a id="12193" href="Veblen.Multinary.html#12182" class="Bound">n</a><a id="12194" class="Symbol">)</a> <a id="12196" href="Veblen.Multinary.html#12172" class="Bound">γ</a> <a id="12198" class="Number">0</a>
  <a id="12202" href="Veblen.Multinary.html#12137" class="Function">φ-α-lim-0</a> <a id="12212" class="Symbol">{</a><a id="12213" class="Argument">α</a> <a id="12215" class="Symbol">=</a> <a id="12217" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12221" class="Symbol">}</a>  <a id="12224" class="Symbol">=</a> <a id="12226" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12233" href="Veblen.Multinary.html#12137" class="Function">φ-α-lim-0</a> <a id="12243" class="Symbol">{</a><a id="12244" class="Argument">α</a> <a id="12246" class="Symbol">=</a> <a id="12248" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12252" class="Symbol">_}</a> <a id="12255" class="Symbol">=</a> <a id="12257" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12264" href="Veblen.Multinary.html#12137" class="Function">φ-α-lim-0</a> <a id="12274" class="Symbol">{</a><a id="12275" class="Argument">α</a> <a id="12277" class="Symbol">=</a> <a id="12279" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12283" href="Veblen.Multinary.html#12283" class="Bound">f</a><a id="12284" class="Symbol">}</a> <a id="12286" class="Symbol">=</a> <a id="12288" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 将 $φ_{α,β}$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β,γ^+} &= \text{fixpt}\kern{0.17em}φ_{α,β,γ} \\
\varphi_{α,β,\text{lim}\kern{0.17em}h} &= \text{jump}\kern{0.17em}λδ,\text{lim}\kern{0.17em}λn,φ_{α,β,h\kern{0.17em}n}\kern{0.17em}δ
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-α-β-suc"></a><a id="12582" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12592" class="Symbol">:</a> <a id="12594" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12596" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12598" href="Veblen.Basic.html#4176" class="Generalizable">β</a> <a id="12600" class="Symbol">(</a><a id="12601" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12605" href="Veblen.Basic.html#4178" class="Generalizable">γ</a><a id="12606" class="Symbol">)</a> <a id="12608" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12610" href="Veblen.Basic.html#13364" class="Function">fixpt</a> <a id="12616" class="Symbol">(</a><a id="12617" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="12619" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="12621" href="Veblen.Basic.html#4176" class="Generalizable">β</a> <a id="12623" href="Veblen.Basic.html#4178" class="Generalizable">γ</a><a id="12624" class="Symbol">)</a>
  <a id="12628" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12638" class="Symbol">{</a><a id="12639" class="Argument">α</a> <a id="12641" class="Symbol">=</a> <a id="12643" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12647" class="Symbol">}</a>  <a id="12650" class="Symbol">{</a><a id="12651" class="Argument">β</a> <a id="12653" class="Symbol">=</a> <a id="12655" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12659" class="Symbol">}</a>  <a id="12662" class="Symbol">=</a> <a id="12664" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12671" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12681" class="Symbol">{</a><a id="12682" class="Argument">α</a> <a id="12684" class="Symbol">=</a> <a id="12686" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12690" class="Symbol">}</a>  <a id="12693" class="Symbol">{</a><a id="12694" class="Argument">β</a> <a id="12696" class="Symbol">=</a> <a id="12698" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12702" class="Symbol">_}</a> <a id="12705" class="Symbol">=</a> <a id="12707" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12714" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12724" class="Symbol">{</a><a id="12725" class="Argument">α</a> <a id="12727" class="Symbol">=</a> <a id="12729" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12733" class="Symbol">}</a>  <a id="12736" class="Symbol">{</a><a id="12737" class="Argument">β</a> <a id="12739" class="Symbol">=</a> <a id="12741" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12745" class="Symbol">_}</a> <a id="12748" class="Symbol">=</a> <a id="12750" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12757" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12767" class="Symbol">{</a><a id="12768" class="Argument">α</a> <a id="12770" class="Symbol">=</a> <a id="12772" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12776" class="Symbol">_}</a> <a id="12779" class="Symbol">{</a><a id="12780" class="Argument">β</a> <a id="12782" class="Symbol">=</a> <a id="12784" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12788" class="Symbol">}</a>  <a id="12791" class="Symbol">=</a> <a id="12793" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12800" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12810" class="Symbol">{</a><a id="12811" class="Argument">α</a> <a id="12813" class="Symbol">=</a> <a id="12815" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12819" class="Symbol">_}</a> <a id="12822" class="Symbol">{</a><a id="12823" class="Argument">β</a> <a id="12825" class="Symbol">=</a> <a id="12827" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12831" class="Symbol">_}</a> <a id="12834" class="Symbol">=</a> <a id="12836" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12843" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12853" class="Symbol">{</a><a id="12854" class="Argument">α</a> <a id="12856" class="Symbol">=</a> <a id="12858" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12862" class="Symbol">_}</a> <a id="12865" class="Symbol">{</a><a id="12866" class="Argument">β</a> <a id="12868" class="Symbol">=</a> <a id="12870" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12874" class="Symbol">_}</a> <a id="12877" class="Symbol">=</a> <a id="12879" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12886" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12896" class="Symbol">{</a><a id="12897" class="Argument">α</a> <a id="12899" class="Symbol">=</a> <a id="12901" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12905" class="Symbol">_}</a> <a id="12908" class="Symbol">{</a><a id="12909" class="Argument">β</a> <a id="12911" class="Symbol">=</a> <a id="12913" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="12917" class="Symbol">}</a>  <a id="12920" class="Symbol">=</a> <a id="12922" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12929" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12939" class="Symbol">{</a><a id="12940" class="Argument">α</a> <a id="12942" class="Symbol">=</a> <a id="12944" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12948" class="Symbol">_}</a> <a id="12951" class="Symbol">{</a><a id="12952" class="Argument">β</a> <a id="12954" class="Symbol">=</a> <a id="12956" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="12960" class="Symbol">_}</a> <a id="12963" class="Symbol">=</a> <a id="12965" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12972" href="Veblen.Multinary.html#12582" class="Function">φ-α-β-suc</a> <a id="12982" class="Symbol">{</a><a id="12983" class="Argument">α</a> <a id="12985" class="Symbol">=</a> <a id="12987" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="12991" class="Symbol">_}</a> <a id="12994" class="Symbol">{</a><a id="12995" class="Argument">β</a> <a id="12997" class="Symbol">=</a> <a id="12999" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13003" class="Symbol">_}</a> <a id="13006" class="Symbol">=</a> <a id="13008" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-α-β-lim"></a><a id="13016" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13026" class="Symbol">:</a> <a id="13028" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="13030" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="13032" href="Veblen.Basic.html#4176" class="Generalizable">β</a> <a id="13034" class="Symbol">(</a><a id="13035" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13039" href="Veblen.Basic.html#9451" class="Generalizable">h</a><a id="13040" class="Symbol">)</a> <a id="13042" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="13044" href="Veblen.Basic.html#11846" class="Function">jump</a> <a id="13049" class="Symbol">λ</a> <a id="13051" href="Veblen.Multinary.html#13051" class="Bound">δ</a> <a id="13053" class="Symbol">→</a> <a id="13055" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13059" class="Symbol">λ</a> <a id="13061" href="Veblen.Multinary.html#13061" class="Bound">n</a> <a id="13063" class="Symbol">→</a> <a id="13065" href="Veblen.Multinary.html#10868" class="Function">φ</a> <a id="13067" href="Veblen.Basic.html#4174" class="Generalizable">α</a> <a id="13069" href="Veblen.Basic.html#4176" class="Generalizable">β</a> <a id="13071" class="Symbol">(</a><a id="13072" href="Veblen.Basic.html#9451" class="Generalizable">h</a> <a id="13074" href="Veblen.Multinary.html#13061" class="Bound">n</a><a id="13075" class="Symbol">)</a> <a id="13077" href="Veblen.Multinary.html#13051" class="Bound">δ</a>
  <a id="13081" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13091" class="Symbol">{</a><a id="13092" class="Argument">α</a> <a id="13094" class="Symbol">=</a> <a id="13096" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13100" class="Symbol">}</a>  <a id="13103" class="Symbol">{</a><a id="13104" class="Argument">β</a> <a id="13106" class="Symbol">=</a> <a id="13108" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13112" class="Symbol">}</a>  <a id="13115" class="Symbol">=</a> <a id="13117" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13124" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13134" class="Symbol">{</a><a id="13135" class="Argument">α</a> <a id="13137" class="Symbol">=</a> <a id="13139" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13143" class="Symbol">}</a>  <a id="13146" class="Symbol">{</a><a id="13147" class="Argument">β</a> <a id="13149" class="Symbol">=</a> <a id="13151" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13155" class="Symbol">_}</a> <a id="13158" class="Symbol">=</a> <a id="13160" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13167" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13177" class="Symbol">{</a><a id="13178" class="Argument">α</a> <a id="13180" class="Symbol">=</a> <a id="13182" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13186" class="Symbol">}</a>  <a id="13189" class="Symbol">{</a><a id="13190" class="Argument">β</a> <a id="13192" class="Symbol">=</a> <a id="13194" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13198" class="Symbol">_}</a> <a id="13201" class="Symbol">=</a> <a id="13203" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13210" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13220" class="Symbol">{</a><a id="13221" class="Argument">α</a> <a id="13223" class="Symbol">=</a> <a id="13225" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13229" class="Symbol">_}</a> <a id="13232" class="Symbol">{</a><a id="13233" class="Argument">β</a> <a id="13235" class="Symbol">=</a> <a id="13237" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13241" class="Symbol">}</a>  <a id="13244" class="Symbol">=</a> <a id="13246" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13253" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13263" class="Symbol">{</a><a id="13264" class="Argument">α</a> <a id="13266" class="Symbol">=</a> <a id="13268" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13272" class="Symbol">_}</a> <a id="13275" class="Symbol">{</a><a id="13276" class="Argument">β</a> <a id="13278" class="Symbol">=</a> <a id="13280" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13284" class="Symbol">_}</a> <a id="13287" class="Symbol">=</a> <a id="13289" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13296" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13306" class="Symbol">{</a><a id="13307" class="Argument">α</a> <a id="13309" class="Symbol">=</a> <a id="13311" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13315" class="Symbol">_}</a> <a id="13318" class="Symbol">{</a><a id="13319" class="Argument">β</a> <a id="13321" class="Symbol">=</a> <a id="13323" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13327" class="Symbol">_}</a> <a id="13330" class="Symbol">=</a> <a id="13332" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13339" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13349" class="Symbol">{</a><a id="13350" class="Argument">α</a> <a id="13352" class="Symbol">=</a> <a id="13354" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13358" class="Symbol">_}</a> <a id="13361" class="Symbol">{</a><a id="13362" class="Argument">β</a> <a id="13364" class="Symbol">=</a> <a id="13366" href="Veblen.Basic.html#3280" class="InductiveConstructor">zero</a><a id="13370" class="Symbol">}</a>  <a id="13373" class="Symbol">=</a> <a id="13375" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13382" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13392" class="Symbol">{</a><a id="13393" class="Argument">α</a> <a id="13395" class="Symbol">=</a> <a id="13397" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13401" class="Symbol">_}</a> <a id="13404" class="Symbol">{</a><a id="13405" class="Argument">β</a> <a id="13407" class="Symbol">=</a> <a id="13409" href="Veblen.Basic.html#3293" class="InductiveConstructor">suc</a> <a id="13413" class="Symbol">_}</a> <a id="13416" class="Symbol">=</a> <a id="13418" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13425" href="Veblen.Multinary.html#13016" class="Function">φ-α-β-lim</a> <a id="13435" class="Symbol">{</a><a id="13436" class="Argument">α</a> <a id="13438" class="Symbol">=</a> <a id="13440" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13444" class="Symbol">_}</a> <a id="13447" class="Symbol">{</a><a id="13448" class="Argument">β</a> <a id="13450" class="Symbol">=</a> <a id="13452" href="Veblen.Basic.html#3312" class="InductiveConstructor">lim</a> <a id="13456" class="Symbol">_}</a> <a id="13459" class="Symbol">=</a> <a id="13461" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**例** 一个很大的大数:

$$
\text{oom}_2 := f_{φ_{Γ_0,0,0}\kern{0.17em}(0)}(99)
$$

<pre class="Agda"><a id="oom₂"></a><a id="13554" href="Veblen.Multinary.html#13554" class="Function">oom₂</a> <a id="13559" class="Symbol">=</a> <a id="13561" href="Veblen.Basic.html#5689" class="Function">FGH.f</a> <a id="13567" class="Symbol">(</a><a id="13568" href="Veblen.Multinary.html#10868" class="Function">QuaternaryVeblen.φ</a> <a id="13587" class="Symbol">(</a><a id="13588" href="Veblen.Multinary.html#4682" class="Function">BinaryVeblen.Γ</a> <a id="13603" class="Number">0</a><a id="13604" class="Symbol">)</a> <a id="13606" class="Number">0</a> <a id="13608" class="Number">0</a> <a id="13610" class="Number">0</a><a id="13611" class="Symbol">)</a> <a id="13613" class="Number">99</a>
</pre>