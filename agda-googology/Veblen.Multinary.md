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
- 起始步骤: $F$
- 递归步骤: 迭代 $\text{fixpt}$
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作

即

$$
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}\text{fixpt}\kern{0.17em}(λφ,\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]\kern{0.17em}β)
$$

<pre class="Agda">  <a id="BinaryVeblen.Φ"></a><a id="2618" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="2620" class="Symbol">:</a> <a id="2622" class="Symbol">(</a><a id="2623" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="2627" class="Symbol">→</a> <a id="2629" href="Veblen.Basic.html#3243" class="Datatype">Ord</a><a id="2632" class="Symbol">)</a> <a id="2634" class="Symbol">→</a> <a id="2636" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="2640" class="Symbol">→</a> <a id="2642" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="2646" class="Symbol">→</a> <a id="2648" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="2654" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="2656" href="Veblen.Multinary.html#2656" class="Bound">F</a> <a id="2658" class="Symbol">=</a> <a id="2660" href="Veblen.Basic.html#8953" class="Function">rec</a> <a id="2664" href="Veblen.Multinary.html#2656" class="Bound">F</a> <a id="2666" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="2672" class="Symbol">(λ</a> <a id="2675" href="Veblen.Multinary.html#2675" class="Bound Operator">φ[_]</a> <a id="2680" class="Symbol">→</a> <a id="2682" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="2687" class="Symbol">λ</a> <a id="2689" href="Veblen.Multinary.html#2689" class="Bound">β</a> <a id="2691" class="Symbol">→</a> <a id="2693" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="2697" class="Symbol">λ</a> <a id="2699" href="Veblen.Multinary.html#2699" class="Bound">n</a> <a id="2701" class="Symbol">→</a> <a id="2703" href="Veblen.Multinary.html#2675" class="Bound Operator">φ[</a> <a id="2706" href="Veblen.Multinary.html#2699" class="Bound">n</a> <a id="2708" href="Veblen.Multinary.html#2675" class="Bound Operator">]</a> <a id="2710" href="Veblen.Multinary.html#2689" class="Bound">β</a><a id="2711" class="Symbol">)</a>
</pre>
**注意** 极限步的跳出操作是反直觉的一步. 从通常的定义式反推不难发现这里需要跳出. 仔细分析二元Veblen函数的序性质才能更好的理解这里跳出的动机, 具体可以参看[Agda大序数(9) 二元Veblen函数](https://zhuanlan.zhihu.com/p/585882648). 这里只需简单的理解为是为了更好的性质和更高的增长率就行了.

**定义** 二元Veblen函数

$$\varphi := Φ\kern{0.17em}λα,ω\kern{0.17em}^α$$

<pre class="Agda">  <a id="BinaryVeblen.φ"></a><a id="2978" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="2980" class="Symbol">:</a> <a id="2982" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="2986" class="Symbol">→</a> <a id="2988" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="2992" class="Symbol">→</a> <a id="2994" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="3000" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3002" class="Symbol">=</a> <a id="3004" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="3006" class="Symbol">(</a><a id="3007" href="Veblen.Basic.html#4617" class="Function">ω</a> <a id="3009" href="Veblen.Basic.html#10933" class="Function Operator">^_</a><a id="3011" class="Symbol">)</a>
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

<pre class="Agda">  <a id="BinaryVeblen.φ-0"></a><a id="3198" href="Veblen.Multinary.html#3198" class="Function">φ-0</a> <a id="3202" class="Symbol">:</a> <a id="3204" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3206" class="Number">0</a> <a id="3208" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3210" href="Veblen.Basic.html#4617" class="Function">ω</a> <a id="3212" href="Veblen.Basic.html#10933" class="Function Operator">^_</a>
  <a id="3217" href="Veblen.Multinary.html#3198" class="Function">φ-0</a> <a id="3221" class="Symbol">=</a> <a id="3223" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-1"></a><a id="3231" href="Veblen.Multinary.html#3231" class="Function">φ-1</a> <a id="3235" class="Symbol">:</a> <a id="3237" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3239" class="Number">1</a> <a id="3241" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3243" href="Veblen.Basic.html#14021" class="Function">ε</a>
  <a id="3247" href="Veblen.Multinary.html#3231" class="Function">φ-1</a> <a id="3251" class="Symbol">=</a> <a id="3253" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-2"></a><a id="3261" href="Veblen.Multinary.html#3261" class="Function">φ-2</a> <a id="3265" class="Symbol">:</a> <a id="3267" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3269" class="Number">2</a> <a id="3271" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3273" href="Veblen.Basic.html#14690" class="Function">ζ</a>
  <a id="3277" href="Veblen.Multinary.html#3261" class="Function">φ-2</a> <a id="3281" class="Symbol">=</a> <a id="3283" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-3"></a><a id="3291" href="Veblen.Multinary.html#3291" class="Function">φ-3</a> <a id="3295" class="Symbol">:</a> <a id="3297" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3299" class="Number">3</a> <a id="3301" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3303" href="Veblen.Basic.html#15159" class="Function">η</a>
  <a id="3307" href="Veblen.Multinary.html#3291" class="Function">φ-3</a> <a id="3311" class="Symbol">=</a> <a id="3313" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+} &= \text{fixpt}\kern{0.17em}φ_α \\
\varphi_{\text{lim}\kern{0.17em}f} &= \text{jump}\kern{0.17em}λα,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}α
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ-suc"></a><a id="3584" href="Veblen.Multinary.html#3584" class="Function">φ-suc</a> <a id="3590" class="Symbol">:</a> <a id="3592" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3594" class="Symbol">(</a><a id="3595" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="3599" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="3600" class="Symbol">)</a> <a id="3602" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3604" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="3610" class="Symbol">(</a><a id="3611" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3613" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="3614" class="Symbol">)</a>
  <a id="3618" href="Veblen.Multinary.html#3584" class="Function">φ-suc</a> <a id="3624" class="Symbol">=</a> <a id="3626" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim"></a><a id="3634" href="Veblen.Multinary.html#3634" class="Function">φ-lim</a> <a id="3640" class="Symbol">:</a> <a id="3642" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3644" class="Symbol">(</a><a id="3645" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="3649" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="3650" class="Symbol">)</a> <a id="3652" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3654" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="3659" class="Symbol">λ</a> <a id="3661" href="Veblen.Multinary.html#3661" class="Bound">α</a> <a id="3663" class="Symbol">→</a> <a id="3665" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="3669" class="Symbol">λ</a> <a id="3671" href="Veblen.Multinary.html#3671" class="Bound">n</a> <a id="3673" class="Symbol">→</a> <a id="3675" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="3677" class="Symbol">(</a><a id="3678" href="Veblen.Basic.html#9423" class="Generalizable">f</a> <a id="3680" href="Veblen.Multinary.html#3671" class="Bound">n</a><a id="3681" class="Symbol">)</a> <a id="3683" href="Veblen.Multinary.html#3661" class="Bound">α</a>
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

<pre class="Agda">  <a id="BinaryVeblen.φ-lim-0"></a><a id="4283" href="Veblen.Multinary.html#4283" class="Function">φ-lim-0</a> <a id="4291" class="Symbol">:</a> <a id="4293" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4295" class="Symbol">(</a><a id="4296" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4300" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="4301" class="Symbol">)</a> <a id="4303" class="Number">0</a> <a id="4305" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4307" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4311" class="Symbol">λ</a> <a id="4313" href="Veblen.Multinary.html#4313" class="Bound">n</a> <a id="4315" class="Symbol">→</a> <a id="4317" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4319" class="Symbol">(</a><a id="4320" href="Veblen.Basic.html#9423" class="Generalizable">f</a> <a id="4322" href="Veblen.Multinary.html#4313" class="Bound">n</a><a id="4323" class="Symbol">)</a> <a id="4325" class="Number">0</a>
  <a id="4329" href="Veblen.Multinary.html#4283" class="Function">φ-lim-0</a> <a id="4337" class="Symbol">=</a> <a id="4339" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim-suc"></a><a id="4347" href="Veblen.Multinary.html#4347" class="Function">φ-lim-suc</a> <a id="4357" class="Symbol">:</a> <a id="4359" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4361" class="Symbol">(</a><a id="4362" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4366" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="4367" class="Symbol">)</a> <a id="4369" class="Symbol">(</a><a id="4370" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="4374" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="4375" class="Symbol">)</a> <a id="4377" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4379" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4383" class="Symbol">λ</a> <a id="4385" href="Veblen.Multinary.html#4385" class="Bound">n</a> <a id="4387" class="Symbol">→</a> <a id="4389" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4391" class="Symbol">(</a><a id="4392" href="Veblen.Basic.html#9423" class="Generalizable">f</a> <a id="4394" href="Veblen.Multinary.html#4385" class="Bound">n</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">(</a><a id="4398" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="4402" class="Symbol">(</a><a id="4403" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4405" class="Symbol">(</a><a id="4406" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4410" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="4411" class="Symbol">)</a> <a id="4413" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="4414" class="Symbol">))</a>
  <a id="4419" href="Veblen.Multinary.html#4347" class="Function">φ-lim-suc</a> <a id="4429" class="Symbol">=</a> <a id="4431" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="BinaryVeblen.φ-lim-lim"></a><a id="4439" href="Veblen.Multinary.html#4439" class="Function">φ-lim-lim</a> <a id="4449" class="Symbol">:</a> <a id="4451" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4453" class="Symbol">(</a><a id="4454" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4458" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="4459" class="Symbol">)</a> <a id="4461" class="Symbol">(</a><a id="4462" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4466" href="Veblen.Basic.html#9425" class="Generalizable">g</a><a id="4467" class="Symbol">)</a> <a id="4469" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4471" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4475" class="Symbol">λ</a> <a id="4477" href="Veblen.Multinary.html#4477" class="Bound">n</a> <a id="4479" class="Symbol">→</a> <a id="4481" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4483" class="Symbol">(</a><a id="4484" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="4488" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="4489" class="Symbol">)</a> <a id="4491" class="Symbol">(</a><a id="4492" href="Veblen.Basic.html#9425" class="Generalizable">g</a> <a id="4494" href="Veblen.Multinary.html#4477" class="Bound">n</a><a id="4495" class="Symbol">)</a>
  <a id="4499" href="Veblen.Multinary.html#4439" class="Function">φ-lim-lim</a> <a id="4509" class="Symbol">=</a> <a id="4511" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
很快, 我们来到了二元Veblen函数的能力极限.

**定义** 对函数 $λα,φ_α\kern{0.17em}0$ 取不动点枚举, 得到的函数称为 $\Gamma$.

$$
\Gamma := \text{fixpt}\kern{0.17em}λα,φ_α\kern{0.17em}0
$$

<pre class="Agda">  <a id="BinaryVeblen.Γ"></a><a id="4682" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4684" class="Symbol">:</a> <a id="4686" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="4690" class="Symbol">→</a> <a id="4692" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="4698" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4700" class="Symbol">=</a> <a id="4702" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="4708" class="Symbol">λ</a> <a id="4710" href="Veblen.Multinary.html#4710" class="Bound">α</a> <a id="4712" class="Symbol">→</a> <a id="4714" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4716" href="Veblen.Multinary.html#4710" class="Bound">α</a> <a id="4718" class="Number">0</a>
</pre>
**例** 最小的 $\Gamma$ 数是

$$Γ_0 = φ_{φ_{φ_{φ_{...}0}\kern{0.17em}0}\kern{0.17em}0}\kern{0.17em}0$$

<pre class="Agda">  <a id="BinaryVeblen.Γ-0"></a><a id="4832" href="Veblen.Multinary.html#4832" class="Function">Γ-0</a> <a id="4836" class="Symbol">:</a> <a id="4838" href="Veblen.Multinary.html#4682" class="Function">Γ</a> <a id="4840" class="Number">0</a> <a id="4842" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4844" href="Veblen.Basic.html#11222" class="Function">iterω</a> <a id="4850" class="Symbol">(λ</a> <a id="4853" href="Veblen.Multinary.html#4853" class="Bound">α</a> <a id="4855" class="Symbol">→</a> <a id="4857" href="Veblen.Multinary.html#2978" class="Function">φ</a> <a id="4859" href="Veblen.Multinary.html#4853" class="Bound">α</a> <a id="4861" class="Number">0</a><a id="4862" class="Symbol">)</a> <a id="4864" class="Number">0</a>
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

<pre class="Agda">  <a id="BinaryVeblen.ε̇"></a><a id="5250" href="Veblen.Multinary.html#5250" class="Function">ε̇</a> <a id="BinaryVeblen.ζ̇"></a><a id="5253" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a> <a id="BinaryVeblen.η̇"></a><a id="5256" href="Veblen.Multinary.html#5256" class="Function">η̇</a> <a id="5259" class="Symbol">:</a> <a id="5261" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="5265" class="Symbol">→</a> <a id="5267" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="5273" href="Veblen.Multinary.html#5250" class="Function">ε̇</a> <a id="5276" class="Symbol">=</a> <a id="5278" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5284" href="Veblen.Multinary.html#4682" class="Function">Γ</a>
  <a id="5288" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a> <a id="5291" class="Symbol">=</a> <a id="5293" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5299" href="Veblen.Multinary.html#5250" class="Function">ε̇</a>
  <a id="5304" href="Veblen.Multinary.html#5256" class="Function">η̇</a> <a id="5307" class="Symbol">=</a> <a id="5309" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5315" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a>
</pre>
然后有第二代 $\varphi$ 和第二代 $\Gamma$ 函数.

$$
\begin{aligned}
\dot{\varphi} &:= Φ\kern{0.17em}Γ \\
\dot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\dot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ̇"></a><a id="5518" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5521" class="Symbol">:</a> <a id="5523" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="5527" class="Symbol">→</a> <a id="5529" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="5533" class="Symbol">→</a> <a id="5535" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="5541" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5544" class="Symbol">=</a> <a id="5546" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="5548" href="Veblen.Multinary.html#4682" class="Function">Γ</a>

  <a id="BinaryVeblen.Γ̇"></a><a id="5553" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a> <a id="5556" class="Symbol">:</a> <a id="5558" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="5562" class="Symbol">→</a> <a id="5564" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="5570" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a> <a id="5573" class="Symbol">=</a> <a id="5575" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5581" class="Symbol">λ</a> <a id="5583" href="Veblen.Multinary.html#5583" class="Bound">α</a> <a id="5585" class="Symbol">→</a> <a id="5587" href="Veblen.Multinary.html#5518" class="Function">φ̇</a> <a id="5590" href="Veblen.Multinary.html#5583" class="Bound">α</a> <a id="5592" class="Number">0</a>
</pre>
乃至第三代 $\varepsilon, \zeta, \eta$ 函数

$$
\begin{aligned}
\ddot{\varepsilon} &:= \text{fixpt}\kern{0.17em}\dot{\Gamma} \\
\ddot{\zeta} &:= \text{fixpt}\kern{0.17em}\ddot{\varepsilon} \\
\ddot{\eta} &:= \text{fixpt}\kern{0.17em}\ddot{\zeta}
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.ε̈"></a><a id="5865" href="Veblen.Multinary.html#5865" class="Function">ε̈</a> <a id="BinaryVeblen.ζ̈"></a><a id="5868" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a> <a id="BinaryVeblen.η̈"></a><a id="5871" href="Veblen.Multinary.html#5871" class="Function">η̈</a> <a id="5874" class="Symbol">:</a> <a id="5876" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="5880" class="Symbol">→</a> <a id="5882" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="5888" href="Veblen.Multinary.html#5865" class="Function">ε̈</a> <a id="5891" class="Symbol">=</a> <a id="5893" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5899" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>
  <a id="5904" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a> <a id="5907" class="Symbol">=</a> <a id="5909" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5915" href="Veblen.Multinary.html#5865" class="Function">ε̈</a>
  <a id="5920" href="Veblen.Multinary.html#5871" class="Function">η̈</a> <a id="5923" class="Symbol">=</a> <a id="5925" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="5931" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a>
</pre>
和第三代 $\varphi$ 和第三代 $\Gamma$ 函数.

$$
\begin{aligned}
\ddot{\varphi} &:= Φ\kern{0.17em}\dot{\Gamma} \\
\ddot{\Gamma} &:= \text{fixpt}\kern{0.17em}λα,\ddot{\varphi}_α\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="BinaryVeblen.φ̈"></a><a id="6146" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6149" class="Symbol">:</a> <a id="6151" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="6155" class="Symbol">→</a> <a id="6157" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="6161" class="Symbol">→</a> <a id="6163" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="6169" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6172" class="Symbol">=</a> <a id="6174" href="Veblen.Multinary.html#2618" class="Function">Φ</a> <a id="6176" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>

  <a id="BinaryVeblen.Γ̈"></a><a id="6182" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a> <a id="6185" class="Symbol">:</a> <a id="6187" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="6191" class="Symbol">→</a> <a id="6193" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="6199" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a> <a id="6202" class="Symbol">=</a> <a id="6204" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="6210" class="Symbol">λ</a> <a id="6212" href="Veblen.Multinary.html#6212" class="Bound">α</a> <a id="6214" class="Symbol">→</a> <a id="6216" href="Veblen.Multinary.html#6146" class="Function">φ̈</a> <a id="6219" href="Veblen.Multinary.html#6212" class="Bound">α</a> <a id="6221" class="Number">0</a>
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

- 起始步骤: $F$
- 递归步骤: 迭代 $λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)$
  - 一些解释
    - 此处迭代的是二元函数 $\text{Ord} → \text{Ord} → \text{Ord}$, 以得到一个三元函数.
    - 参数 $φ_α$ 是上一步的结果, 它是一个二元函数, 看作是对三元函数 $φ$ 输入了上一步的编号 $α$ 所得到的结果.
    - 这一步我们先对 $λβ,φ_{α,β}\kern{0.17em}0$ 取不动点枚举, 再交给二元 $Φ$ 处理
      - 回想上一小节我们是怎么从一代 $φ$ 得到二代 $φ$ 的, 这里的处理方式就是对该操作的反映.
  - 注意: 对任意元 $φ$, 我们都是取第二个参数的不动点枚举, 而对右边剩下的参数全部填零. 二元 $Φ$ 的时候这个规律还看不出来, 现在才显现出来.
- 极限步骤: 对步骤的基本列取极限, 再做一次跳出操作, 再交给二元 $Φ$ 处理
  - 注意: 与递归步骤类似地, 这里是对第二个参数跳出, 右边其余参数全部填零.

即

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β}\kern{0.17em}0)) \\
&(λφ,\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_β\kern{0.17em}0))
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.Φ"></a><a id="7437" href="Veblen.Multinary.html#7437" class="Function">Φ</a> <a id="7439" class="Symbol">:</a> <a id="7441" class="Symbol">(</a><a id="7442" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7446" class="Symbol">→</a> <a id="7448" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7452" class="Symbol">→</a> <a id="7454" href="Veblen.Basic.html#3243" class="Datatype">Ord</a><a id="7457" class="Symbol">)</a> <a id="7459" class="Symbol">→</a> <a id="7461" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7465" class="Symbol">→</a> <a id="7467" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7471" class="Symbol">→</a> <a id="7473" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7477" class="Symbol">→</a> <a id="7479" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="7485" href="Veblen.Multinary.html#7437" class="Function">Φ</a> <a id="7487" href="Veblen.Multinary.html#7487" class="Bound">F</a> <a id="7489" class="Symbol">=</a> <a id="7491" href="Veblen.Basic.html#8953" class="Function">rec</a> <a id="7495" href="Veblen.Multinary.html#7487" class="Bound">F</a>
    <a id="7501" class="Symbol">(λ</a> <a id="7504" href="Veblen.Multinary.html#7504" class="Bound">φ-α</a>  <a id="7509" class="Symbol">→</a> <a id="7511" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="7517" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="7519" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="7525" class="Symbol">λ</a> <a id="7527" href="Veblen.Multinary.html#7527" class="Bound">β</a> <a id="7529" class="Symbol">→</a> <a id="7531" href="Veblen.Multinary.html#7504" class="Bound">φ-α</a> <a id="7535" href="Veblen.Multinary.html#7527" class="Bound">β</a> <a id="7537" class="Number">0</a><a id="7538" class="Symbol">)</a>
    <a id="7544" class="Symbol">(λ</a> <a id="7547" href="Veblen.Multinary.html#7547" class="Bound Operator">φ[_]</a> <a id="7552" class="Symbol">→</a> <a id="7554" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="7560" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="7562" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="7567" class="Symbol">λ</a> <a id="7569" href="Veblen.Multinary.html#7569" class="Bound">β</a> <a id="7571" class="Symbol">→</a> <a id="7573" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="7577" class="Symbol">λ</a> <a id="7579" href="Veblen.Multinary.html#7579" class="Bound">n</a> <a id="7581" class="Symbol">→</a> <a id="7583" href="Veblen.Multinary.html#7547" class="Bound Operator">φ[</a> <a id="7586" href="Veblen.Multinary.html#7579" class="Bound">n</a> <a id="7588" href="Veblen.Multinary.html#7547" class="Bound Operator">]</a> <a id="7590" href="Veblen.Multinary.html#7569" class="Bound">β</a> <a id="7592" class="Number">0</a><a id="7593" class="Symbol">)</a>
</pre>
**定义** 三元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Bin}.\varphi$$

<pre class="Agda">  <a id="TrinaryVeblen.φ"></a><a id="7678" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="7680" class="Symbol">:</a> <a id="7682" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7686" class="Symbol">→</a> <a id="7688" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7692" class="Symbol">→</a> <a id="7694" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="7698" class="Symbol">→</a> <a id="7700" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="7706" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="7708" class="Symbol">=</a> <a id="7710" href="Veblen.Multinary.html#7437" class="Function">Φ</a> <a id="7712" href="Veblen.Multinary.html#2978" class="Function">Bin.φ</a>
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

<pre class="Agda">  <a id="TrinaryVeblen.φ-0"></a><a id="8189" href="Veblen.Multinary.html#8189" class="Function">φ-0</a> <a id="8193" class="Symbol">:</a> <a id="8195" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8197" class="Number">0</a> <a id="8199" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8201" href="Veblen.Multinary.html#2978" class="Function">Bin.φ</a>
  <a id="8209" href="Veblen.Multinary.html#8189" class="Function">φ-0</a> <a id="8213" class="Symbol">=</a> <a id="8215" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-0"></a><a id="8223" href="Veblen.Multinary.html#8223" class="Function">φ-1-0</a> <a id="8229" class="Symbol">:</a> <a id="8231" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8233" class="Number">1</a> <a id="8235" class="Number">0</a> <a id="8237" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8239" href="Veblen.Multinary.html#4682" class="Function">Γ</a>
  <a id="8243" href="Veblen.Multinary.html#8223" class="Function">φ-1-0</a> <a id="8249" class="Symbol">=</a> <a id="8251" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-1"></a><a id="8259" href="Veblen.Multinary.html#8259" class="Function">φ-1-1</a> <a id="8265" class="Symbol">:</a> <a id="8267" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8269" class="Number">1</a> <a id="8271" class="Number">1</a> <a id="8273" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8275" href="Veblen.Multinary.html#5250" class="Function">ε̇</a>
  <a id="8280" href="Veblen.Multinary.html#8259" class="Function">φ-1-1</a> <a id="8286" class="Symbol">=</a> <a id="8288" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-2"></a><a id="8296" href="Veblen.Multinary.html#8296" class="Function">φ-1-2</a> <a id="8302" class="Symbol">:</a> <a id="8304" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8306" class="Number">1</a> <a id="8308" class="Number">2</a> <a id="8310" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8312" href="Veblen.Multinary.html#5253" class="Function">ζ̇</a>
  <a id="8317" href="Veblen.Multinary.html#8296" class="Function">φ-1-2</a> <a id="8323" class="Symbol">=</a> <a id="8325" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1-3"></a><a id="8333" href="Veblen.Multinary.html#8333" class="Function">φ-1-3</a> <a id="8339" class="Symbol">:</a> <a id="8341" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8343" class="Number">1</a> <a id="8345" class="Number">3</a> <a id="8347" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8349" href="Veblen.Multinary.html#5256" class="Function">η̇</a>
  <a id="8354" href="Veblen.Multinary.html#8333" class="Function">φ-1-3</a> <a id="8360" class="Symbol">=</a> <a id="8362" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-1"></a><a id="8370" href="Veblen.Multinary.html#8370" class="Function">φ-1</a> <a id="8374" class="Symbol">:</a> <a id="8376" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8378" class="Number">1</a> <a id="8380" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8382" href="Veblen.Multinary.html#5518" class="Function">φ̇</a>
  <a id="8387" href="Veblen.Multinary.html#8370" class="Function">φ-1</a> <a id="8391" class="Symbol">=</a> <a id="8393" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-0"></a><a id="8401" href="Veblen.Multinary.html#8401" class="Function">φ-2-0</a> <a id="8407" class="Symbol">:</a> <a id="8409" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8411" class="Number">2</a> <a id="8413" class="Number">0</a> <a id="8415" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8417" href="Veblen.Multinary.html#5553" class="Function">Γ̇</a>
  <a id="8422" href="Veblen.Multinary.html#8401" class="Function">φ-2-0</a> <a id="8428" class="Symbol">=</a> <a id="8430" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-1"></a><a id="8438" href="Veblen.Multinary.html#8438" class="Function">φ-2-1</a> <a id="8444" class="Symbol">:</a> <a id="8446" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8448" class="Number">2</a> <a id="8450" class="Number">1</a> <a id="8452" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8454" href="Veblen.Multinary.html#5865" class="Function">ε̈</a>
  <a id="8459" href="Veblen.Multinary.html#8438" class="Function">φ-2-1</a> <a id="8465" class="Symbol">=</a> <a id="8467" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-2"></a><a id="8475" href="Veblen.Multinary.html#8475" class="Function">φ-2-2</a> <a id="8481" class="Symbol">:</a> <a id="8483" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8485" class="Number">2</a> <a id="8487" class="Number">2</a> <a id="8489" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8491" href="Veblen.Multinary.html#5868" class="Function">ζ̈</a>
  <a id="8496" href="Veblen.Multinary.html#8475" class="Function">φ-2-2</a> <a id="8502" class="Symbol">=</a> <a id="8504" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2-3"></a><a id="8512" href="Veblen.Multinary.html#8512" class="Function">φ-2-3</a> <a id="8518" class="Symbol">:</a> <a id="8520" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8522" class="Number">2</a> <a id="8524" class="Number">3</a> <a id="8526" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8528" href="Veblen.Multinary.html#5871" class="Function">η̈</a>
  <a id="8533" href="Veblen.Multinary.html#8512" class="Function">φ-2-3</a> <a id="8539" class="Symbol">=</a> <a id="8541" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-2"></a><a id="8549" href="Veblen.Multinary.html#8549" class="Function">φ-2</a> <a id="8553" class="Symbol">:</a> <a id="8555" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8557" class="Number">2</a> <a id="8559" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8561" href="Veblen.Multinary.html#6146" class="Function">φ̈</a>
  <a id="8566" href="Veblen.Multinary.html#8549" class="Function">φ-2</a> <a id="8570" class="Symbol">=</a> <a id="8572" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-3-0"></a><a id="8580" href="Veblen.Multinary.html#8580" class="Function">φ-3-0</a> <a id="8586" class="Symbol">:</a> <a id="8588" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8590" class="Number">3</a> <a id="8592" class="Number">0</a> <a id="8594" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8596" href="Veblen.Multinary.html#6182" class="Function">Γ̈</a>
  <a id="8601" href="Veblen.Multinary.html#8580" class="Function">φ-3-0</a> <a id="8607" class="Symbol">=</a> <a id="8609" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为后继的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0} &= \text{fixpt}λβ,φ_{α,β}\kern{0.17em}0 \\
\varphi_{α^+,β^+} &= \text{fixpt}\kern{0.17em}φ_{α^+,β} \\
\varphi_{α^+,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α^+,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.φ-suc-0"></a><a id="8969" href="Veblen.Multinary.html#8969" class="Function">φ-suc-0</a> <a id="8977" class="Symbol">:</a> <a id="8979" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="8981" class="Symbol">(</a><a id="8982" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="8986" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="8987" class="Symbol">)</a> <a id="8989" class="Number">0</a> <a id="8991" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="8993" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="8999" class="Symbol">λ</a> <a id="9001" href="Veblen.Multinary.html#9001" class="Bound">β</a> <a id="9003" class="Symbol">→</a> <a id="9005" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9007" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="9009" href="Veblen.Multinary.html#9001" class="Bound">β</a> <a id="9011" class="Number">0</a>
  <a id="9015" href="Veblen.Multinary.html#8969" class="Function">φ-suc-0</a> <a id="9023" class="Symbol">=</a> <a id="9025" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-suc-suc"></a><a id="9033" href="Veblen.Multinary.html#9033" class="Function">φ-suc-suc</a> <a id="9043" class="Symbol">:</a> <a id="9045" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9047" class="Symbol">(</a><a id="9048" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9052" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="9053" class="Symbol">)</a> <a id="9055" class="Symbol">(</a><a id="9056" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9060" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="9061" class="Symbol">)</a> <a id="9063" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9065" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="9071" class="Symbol">(</a><a id="9072" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9074" class="Symbol">(</a><a id="9075" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9079" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="9080" class="Symbol">)</a> <a id="9082" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="9083" class="Symbol">)</a>
  <a id="9087" href="Veblen.Multinary.html#9033" class="Function">φ-suc-suc</a> <a id="9097" class="Symbol">=</a> <a id="9099" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-suc-lim"></a><a id="9107" href="Veblen.Multinary.html#9107" class="Function">φ-suc-lim</a> <a id="9117" class="Symbol">:</a> <a id="9119" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9121" class="Symbol">(</a><a id="9122" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9126" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="9127" class="Symbol">)</a> <a id="9129" class="Symbol">(</a><a id="9130" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9134" href="Veblen.Basic.html#9425" class="Generalizable">g</a><a id="9135" class="Symbol">)</a> <a id="9137" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9139" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="9144" class="Symbol">λ</a> <a id="9146" href="Veblen.Multinary.html#9146" class="Bound">γ</a> <a id="9148" class="Symbol">→</a> <a id="9150" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9154" class="Symbol">λ</a> <a id="9156" href="Veblen.Multinary.html#9156" class="Bound">n</a> <a id="9158" class="Symbol">→</a> <a id="9160" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9162" class="Symbol">(</a><a id="9163" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9167" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="9168" class="Symbol">)</a> <a id="9170" class="Symbol">(</a><a id="9171" href="Veblen.Basic.html#9425" class="Generalizable">g</a> <a id="9173" href="Veblen.Multinary.html#9156" class="Bound">n</a><a id="9174" class="Symbol">)</a> <a id="9176" href="Veblen.Multinary.html#9146" class="Bound">γ</a>
  <a id="9180" href="Veblen.Multinary.html#9107" class="Function">φ-suc-lim</a> <a id="9190" class="Symbol">=</a> <a id="9192" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 对于第一个参数为极限的情况, 我们对第二个参数分情况讨论, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,β^+} &= \text{fixpt}\kern{0.17em}φ_{\text{lim}\kern{0.17em}f,β}\kern{0.17em} \\
\varphi_{\text{lim}\kern{0.17em}f,\text{lim}\kern{0.17em}g} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f,g\kern{0.17em}n}\kern{0.17em}γ
\end{aligned}
$$

<pre class="Agda">  <a id="TrinaryVeblen.φ-lim-0"></a><a id="9722" href="Veblen.Multinary.html#9722" class="Function">φ-lim-0</a> <a id="9730" class="Symbol">:</a> <a id="9732" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9734" class="Symbol">(</a><a id="9735" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9739" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="9740" class="Symbol">)</a> <a id="9742" class="Number">0</a> <a id="9744" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9746" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="9751" class="Symbol">λ</a> <a id="9753" href="Veblen.Multinary.html#9753" class="Bound">β</a> <a id="9755" class="Symbol">→</a> <a id="9757" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9761" class="Symbol">λ</a> <a id="9763" href="Veblen.Multinary.html#9763" class="Bound">n</a> <a id="9765" class="Symbol">→</a> <a id="9767" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9769" class="Symbol">(</a><a id="9770" href="Veblen.Basic.html#9423" class="Generalizable">f</a> <a id="9772" href="Veblen.Multinary.html#9763" class="Bound">n</a><a id="9773" class="Symbol">)</a> <a id="9775" href="Veblen.Multinary.html#9753" class="Bound">β</a> <a id="9777" class="Number">0</a>
  <a id="9781" href="Veblen.Multinary.html#9722" class="Function">φ-lim-0</a> <a id="9789" class="Symbol">=</a> <a id="9791" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-lim-suc"></a><a id="9799" href="Veblen.Multinary.html#9799" class="Function">φ-lim-suc</a> <a id="9809" class="Symbol">:</a> <a id="9811" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9813" class="Symbol">(</a><a id="9814" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9818" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="9819" class="Symbol">)</a> <a id="9821" class="Symbol">(</a><a id="9822" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="9826" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="9827" class="Symbol">)</a> <a id="9829" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9831" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="9837" class="Symbol">(</a><a id="9838" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9840" class="Symbol">(</a><a id="9841" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9845" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="9846" class="Symbol">)</a> <a id="9848" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="9849" class="Symbol">)</a>
  <a id="9853" href="Veblen.Multinary.html#9799" class="Function">φ-lim-suc</a> <a id="9863" class="Symbol">=</a> <a id="9865" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="TrinaryVeblen.φ-lim-lim"></a><a id="9873" href="Veblen.Multinary.html#9873" class="Function">φ-lim-lim</a> <a id="9883" class="Symbol">:</a> <a id="9885" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9887" class="Symbol">(</a><a id="9888" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9892" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="9893" class="Symbol">)</a> <a id="9895" class="Symbol">(</a><a id="9896" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9900" href="Veblen.Basic.html#9425" class="Generalizable">g</a><a id="9901" class="Symbol">)</a> <a id="9903" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9905" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="9910" class="Symbol">λ</a> <a id="9912" href="Veblen.Multinary.html#9912" class="Bound">γ</a> <a id="9914" class="Symbol">→</a> <a id="9916" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9920" class="Symbol">λ</a> <a id="9922" href="Veblen.Multinary.html#9922" class="Bound">n</a> <a id="9924" class="Symbol">→</a> <a id="9926" href="Veblen.Multinary.html#7678" class="Function">φ</a> <a id="9928" class="Symbol">(</a><a id="9929" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="9933" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="9934" class="Symbol">)</a> <a id="9936" class="Symbol">(</a><a id="9937" href="Veblen.Basic.html#9425" class="Generalizable">g</a> <a id="9939" href="Veblen.Multinary.html#9922" class="Bound">n</a><a id="9940" class="Symbol">)</a> <a id="9942" href="Veblen.Multinary.html#9912" class="Bound">γ</a>
  <a id="9946" href="Veblen.Multinary.html#9873" class="Function">φ-lim-lim</a> <a id="9956" class="Symbol">=</a> <a id="9958" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
## 四元Veblen函数

<pre class="Agda"><a id="9991" class="Keyword">module</a> <a id="QuaternaryVeblen"></a><a id="9998" href="Veblen.Multinary.html#9998" class="Module">QuaternaryVeblen</a> <a id="10015" class="Keyword">where</a>
  <a id="10023" class="Keyword">private</a> <a id="10031" class="Keyword">module</a> <a id="QuaternaryVeblen.Bin"></a><a id="10038" href="Veblen.Multinary.html#10038" class="Module">Bin</a> <a id="10042" class="Symbol">=</a> <a id="10044" href="Veblen.Multinary.html#2103" class="Module">BinaryVeblen</a>
  <a id="10059" class="Keyword">private</a> <a id="10067" class="Keyword">module</a> <a id="QuaternaryVeblen.Tri"></a><a id="10074" href="Veblen.Multinary.html#10074" class="Module">Tri</a> <a id="10078" class="Symbol">=</a> <a id="10080" href="Veblen.Multinary.html#6296" class="Module">TrinaryVeblen</a>
</pre>
摸清二元到三元的规律之后, 三元到四元就是按部就班的操作了.

**定义** 四元版本的 $Φ$ 为, 对给定的序数函数 $F : \text{Ord} → \text{Ord} → \text{Ord} → \text{Ord}$, 使用 $\text{rec}$

$$
\begin{aligned}
Φ\kern{0.17em}F := \text{rec}\kern{0.17em}F\kern{0.17em}&(λφ_α,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0))) \\
&(λφ,\text{Tri}.Φ\kern{0.17em}(\text{Bin}.Φ\kern{0.17em}(\text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ[ n ]_{β,0}\kern{0.17em}0)))
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.Φ"></a><a id="10594" href="Veblen.Multinary.html#10594" class="Function">Φ</a> <a id="10596" class="Symbol">:</a> <a id="10598" class="Symbol">(</a><a id="10599" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10603" class="Symbol">→</a> <a id="10605" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10609" class="Symbol">→</a> <a id="10611" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10615" class="Symbol">→</a> <a id="10617" href="Veblen.Basic.html#3243" class="Datatype">Ord</a><a id="10620" class="Symbol">)</a> <a id="10622" class="Symbol">→</a> <a id="10624" class="Symbol">(</a><a id="10625" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10629" class="Symbol">→</a> <a id="10631" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10635" class="Symbol">→</a> <a id="10637" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10641" class="Symbol">→</a> <a id="10643" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10647" class="Symbol">→</a> <a id="10649" href="Veblen.Basic.html#3243" class="Datatype">Ord</a><a id="10652" class="Symbol">)</a>
  <a id="10656" href="Veblen.Multinary.html#10594" class="Function">Φ</a> <a id="10658" href="Veblen.Multinary.html#10658" class="Bound">F</a> <a id="10660" class="Symbol">=</a> <a id="10662" href="Veblen.Basic.html#8953" class="Function">rec</a> <a id="10666" href="Veblen.Multinary.html#10658" class="Bound">F</a>
    <a id="10672" class="Symbol">(λ</a> <a id="10675" href="Veblen.Multinary.html#10675" class="Bound">φ-α</a>  <a id="10680" class="Symbol">→</a> <a id="10682" href="Veblen.Multinary.html#7437" class="Function">Tri.Φ</a> <a id="10688" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10690" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="10696" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10698" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="10704" class="Symbol">λ</a> <a id="10706" href="Veblen.Multinary.html#10706" class="Bound">β</a> <a id="10708" class="Symbol">→</a> <a id="10710" href="Veblen.Multinary.html#10675" class="Bound">φ-α</a> <a id="10714" href="Veblen.Multinary.html#10706" class="Bound">β</a> <a id="10716" class="Number">0</a> <a id="10718" class="Number">0</a><a id="10719" class="Symbol">)</a>
    <a id="10725" class="Symbol">(λ</a> <a id="10728" href="Veblen.Multinary.html#10728" class="Bound Operator">φ[_]</a> <a id="10733" class="Symbol">→</a> <a id="10735" href="Veblen.Multinary.html#7437" class="Function">Tri.Φ</a> <a id="10741" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10743" href="Veblen.Multinary.html#2618" class="Function">Bin.Φ</a> <a id="10749" href="Function.Base.html#1974" class="Function Operator">$</a> <a id="10751" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="10756" class="Symbol">λ</a> <a id="10758" href="Veblen.Multinary.html#10758" class="Bound">β</a> <a id="10760" class="Symbol">→</a> <a id="10762" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="10766" class="Symbol">λ</a> <a id="10768" href="Veblen.Multinary.html#10768" class="Bound">n</a> <a id="10770" class="Symbol">→</a> <a id="10772" href="Veblen.Multinary.html#10728" class="Bound Operator">φ[</a> <a id="10775" href="Veblen.Multinary.html#10768" class="Bound">n</a> <a id="10777" href="Veblen.Multinary.html#10728" class="Bound Operator">]</a> <a id="10779" href="Veblen.Multinary.html#10758" class="Bound">β</a> <a id="10781" class="Number">0</a> <a id="10783" class="Number">0</a><a id="10784" class="Symbol">)</a>
</pre>
**定义** 四元Veblen函数

$$\varphi := Φ\kern{0.17em}\text{Tri}.\varphi$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ"></a><a id="10869" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="10871" class="Symbol">:</a> <a id="10873" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10877" class="Symbol">→</a> <a id="10879" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10883" class="Symbol">→</a> <a id="10885" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10889" class="Symbol">→</a> <a id="10891" href="Veblen.Basic.html#3243" class="Datatype">Ord</a> <a id="10895" class="Symbol">→</a> <a id="10897" href="Veblen.Basic.html#3243" class="Datatype">Ord</a>
  <a id="10903" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="10905" class="Symbol">=</a> <a id="10907" href="Veblen.Multinary.html#10594" class="Function">Φ</a> <a id="10909" href="Veblen.Multinary.html#7678" class="Function">Tri.φ</a>
</pre>
**例** 第一个参数从无效到刚开始生效, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_0 &= \text{Tri}.\varphi \\
\varphi_{1,0,0} &= \text{fixpt}\kern{0.17em}λα,\text{Tri}.\varphi_{α,0}\kern{0.17em}0 \\
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-0"></a><a id="11128" href="Veblen.Multinary.html#11128" class="Function">φ-0</a> <a id="11132" class="Symbol">:</a> <a id="11134" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11136" class="Number">0</a> <a id="11138" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11140" href="Veblen.Multinary.html#7678" class="Function">Tri.φ</a>
  <a id="11148" href="Veblen.Multinary.html#11128" class="Function">φ-0</a> <a id="11152" class="Symbol">=</a> <a id="11154" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-1-0-0"></a><a id="11162" href="Veblen.Multinary.html#11162" class="Function">φ-1-0-0</a> <a id="11170" class="Symbol">:</a> <a id="11172" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11174" class="Number">1</a> <a id="11176" class="Number">0</a> <a id="11178" class="Number">0</a> <a id="11180" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11182" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="11188" class="Symbol">(λ</a> <a id="11191" href="Veblen.Multinary.html#11191" class="Bound">α</a> <a id="11193" class="Symbol">→</a> <a id="11195" href="Veblen.Multinary.html#7678" class="Function">Tri.φ</a> <a id="11201" href="Veblen.Multinary.html#11191" class="Bound">α</a> <a id="11203" class="Number">0</a> <a id="11205" class="Number">0</a><a id="11206" class="Symbol">)</a>
  <a id="11210" href="Veblen.Multinary.html#11162" class="Function">φ-1-0-0</a> <a id="11218" class="Symbol">=</a> <a id="11220" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 中间两个参数为零, 讨论第一个参数为后继和极限的情况, 由定义, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α^+,0,0} &= \text{fixpt}\kern{0.17em}λβ,φ_{α,β,0}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f,0,0} &= \text{jump}\kern{0.17em}λβ,\text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n,β,0}\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-suc-0-0"></a><a id="11536" href="Veblen.Multinary.html#11536" class="Function">φ-suc-0-0</a> <a id="11546" class="Symbol">:</a> <a id="11548" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11550" class="Symbol">(</a><a id="11551" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="11555" href="Veblen.Basic.html#4150" class="Generalizable">α</a><a id="11556" class="Symbol">)</a> <a id="11558" class="Number">0</a> <a id="11560" class="Number">0</a> <a id="11562" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11564" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="11570" class="Symbol">λ</a> <a id="11572" href="Veblen.Multinary.html#11572" class="Bound">β</a> <a id="11574" class="Symbol">→</a> <a id="11576" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11578" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="11580" href="Veblen.Multinary.html#11572" class="Bound">β</a> <a id="11582" class="Number">0</a> <a id="11584" class="Number">0</a>
  <a id="11588" href="Veblen.Multinary.html#11536" class="Function">φ-suc-0-0</a> <a id="11598" class="Symbol">=</a> <a id="11600" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-lim-0-0"></a><a id="11608" href="Veblen.Multinary.html#11608" class="Function">φ-lim-0-0</a> <a id="11618" class="Symbol">:</a> <a id="11620" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11622" class="Symbol">(</a><a id="11623" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="11627" href="Veblen.Basic.html#9423" class="Generalizable">f</a><a id="11628" class="Symbol">)</a> <a id="11630" class="Number">0</a> <a id="11632" class="Number">0</a> <a id="11634" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="11636" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="11641" class="Symbol">λ</a> <a id="11643" href="Veblen.Multinary.html#11643" class="Bound">β</a> <a id="11645" class="Symbol">→</a> <a id="11647" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="11651" class="Symbol">λ</a> <a id="11653" href="Veblen.Multinary.html#11653" class="Bound">n</a> <a id="11655" class="Symbol">→</a> <a id="11657" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="11659" class="Symbol">(</a><a id="11660" href="Veblen.Basic.html#9423" class="Generalizable">f</a> <a id="11662" href="Veblen.Multinary.html#11653" class="Bound">n</a><a id="11663" class="Symbol">)</a> <a id="11665" href="Veblen.Multinary.html#11643" class="Bound">β</a> <a id="11667" class="Number">0</a> <a id="11669" class="Number">0</a>
  <a id="11673" href="Veblen.Multinary.html#11608" class="Function">φ-lim-0-0</a> <a id="11683" class="Symbol">=</a> <a id="11685" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 将 $φ_α$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β^+,0} &= \text{fixpt}\kern{0.17em}λγ,φ_{α,β,γ}\kern{0.17em}0 \\
\varphi_{α,\text{lim}\kern{0.17em}g,0} &= \text{jump}\kern{0.17em}λγ,\text{lim}\kern{0.17em}λn,φ_{α,g\kern{0.17em}n,γ}\kern{0.17em}0
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-α-suc-0"></a><a id="11992" href="Veblen.Multinary.html#11992" class="Function">φ-α-suc-0</a> <a id="12002" class="Symbol">:</a> <a id="12004" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12006" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12008" class="Symbol">(</a><a id="12009" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12013" href="Veblen.Basic.html#4152" class="Generalizable">β</a><a id="12014" class="Symbol">)</a> <a id="12016" class="Number">0</a> <a id="12018" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12020" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="12026" class="Symbol">λ</a> <a id="12028" href="Veblen.Multinary.html#12028" class="Bound">γ</a> <a id="12030" class="Symbol">→</a> <a id="12032" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12034" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12036" href="Veblen.Basic.html#4152" class="Generalizable">β</a> <a id="12038" href="Veblen.Multinary.html#12028" class="Bound">γ</a> <a id="12040" class="Number">0</a>
  <a id="12044" href="Veblen.Multinary.html#11992" class="Function">φ-α-suc-0</a> <a id="12054" class="Symbol">{</a><a id="12055" class="Argument">α</a> <a id="12057" class="Symbol">=</a> <a id="12059" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12063" class="Symbol">}</a>  <a id="12066" class="Symbol">=</a> <a id="12068" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12075" href="Veblen.Multinary.html#11992" class="Function">φ-α-suc-0</a> <a id="12085" class="Symbol">{</a><a id="12086" class="Argument">α</a> <a id="12088" class="Symbol">=</a> <a id="12090" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12094" class="Symbol">_}</a> <a id="12097" class="Symbol">=</a> <a id="12099" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12106" href="Veblen.Multinary.html#11992" class="Function">φ-α-suc-0</a> <a id="12116" class="Symbol">{</a><a id="12117" class="Argument">α</a> <a id="12119" class="Symbol">=</a> <a id="12121" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12125" href="Veblen.Multinary.html#12125" class="Bound">f</a><a id="12126" class="Symbol">}</a> <a id="12128" class="Symbol">=</a> <a id="12130" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-α-lim-0"></a><a id="12138" href="Veblen.Multinary.html#12138" class="Function">φ-α-lim-0</a> <a id="12148" class="Symbol">:</a> <a id="12150" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12152" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12154" class="Symbol">(</a><a id="12155" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12159" href="Veblen.Basic.html#9425" class="Generalizable">g</a><a id="12160" class="Symbol">)</a> <a id="12162" class="Number">0</a> <a id="12164" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12166" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="12171" class="Symbol">λ</a> <a id="12173" href="Veblen.Multinary.html#12173" class="Bound">γ</a> <a id="12175" class="Symbol">→</a> <a id="12177" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12181" class="Symbol">λ</a> <a id="12183" href="Veblen.Multinary.html#12183" class="Bound">n</a> <a id="12185" class="Symbol">→</a> <a id="12187" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12189" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12191" class="Symbol">(</a><a id="12192" href="Veblen.Basic.html#9425" class="Generalizable">g</a> <a id="12194" href="Veblen.Multinary.html#12183" class="Bound">n</a><a id="12195" class="Symbol">)</a> <a id="12197" href="Veblen.Multinary.html#12173" class="Bound">γ</a> <a id="12199" class="Number">0</a>
  <a id="12203" href="Veblen.Multinary.html#12138" class="Function">φ-α-lim-0</a> <a id="12213" class="Symbol">{</a><a id="12214" class="Argument">α</a> <a id="12216" class="Symbol">=</a> <a id="12218" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12222" class="Symbol">}</a>  <a id="12225" class="Symbol">=</a> <a id="12227" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12234" href="Veblen.Multinary.html#12138" class="Function">φ-α-lim-0</a> <a id="12244" class="Symbol">{</a><a id="12245" class="Argument">α</a> <a id="12247" class="Symbol">=</a> <a id="12249" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12253" class="Symbol">_}</a> <a id="12256" class="Symbol">=</a> <a id="12258" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12265" href="Veblen.Multinary.html#12138" class="Function">φ-α-lim-0</a> <a id="12275" class="Symbol">{</a><a id="12276" class="Argument">α</a> <a id="12278" class="Symbol">=</a> <a id="12280" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12284" href="Veblen.Multinary.html#12284" class="Bound">f</a><a id="12285" class="Symbol">}</a> <a id="12287" class="Symbol">=</a> <a id="12289" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**定理** 将 $φ_{α,β}$ 看作一个固定的函数, 类似地, 有以下等式成立.

$$
\begin{aligned}
\varphi_{α,β,γ^+} &= \text{fixpt}\kern{0.17em}φ_{α,β,γ} \\
\varphi_{α,β,\text{lim}\kern{0.17em}h} &= \text{jump}\kern{0.17em}λδ,\text{lim}\kern{0.17em}λn,φ_{α,β,h\kern{0.17em}n}\kern{0.17em}δ
\end{aligned}
$$

<pre class="Agda">  <a id="QuaternaryVeblen.φ-α-β-suc"></a><a id="12583" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12593" class="Symbol">:</a> <a id="12595" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12597" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12599" href="Veblen.Basic.html#4152" class="Generalizable">β</a> <a id="12601" class="Symbol">(</a><a id="12602" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12606" href="Veblen.Basic.html#4154" class="Generalizable">γ</a><a id="12607" class="Symbol">)</a> <a id="12609" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="12611" href="Veblen.Basic.html#13103" class="Function">fixpt</a> <a id="12617" class="Symbol">(</a><a id="12618" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="12620" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="12622" href="Veblen.Basic.html#4152" class="Generalizable">β</a> <a id="12624" href="Veblen.Basic.html#4154" class="Generalizable">γ</a><a id="12625" class="Symbol">)</a>
  <a id="12629" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12639" class="Symbol">{</a><a id="12640" class="Argument">α</a> <a id="12642" class="Symbol">=</a> <a id="12644" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12648" class="Symbol">}</a>  <a id="12651" class="Symbol">{</a><a id="12652" class="Argument">β</a> <a id="12654" class="Symbol">=</a> <a id="12656" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12660" class="Symbol">}</a>  <a id="12663" class="Symbol">=</a> <a id="12665" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12672" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12682" class="Symbol">{</a><a id="12683" class="Argument">α</a> <a id="12685" class="Symbol">=</a> <a id="12687" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12691" class="Symbol">}</a>  <a id="12694" class="Symbol">{</a><a id="12695" class="Argument">β</a> <a id="12697" class="Symbol">=</a> <a id="12699" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12703" class="Symbol">_}</a> <a id="12706" class="Symbol">=</a> <a id="12708" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12715" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12725" class="Symbol">{</a><a id="12726" class="Argument">α</a> <a id="12728" class="Symbol">=</a> <a id="12730" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12734" class="Symbol">}</a>  <a id="12737" class="Symbol">{</a><a id="12738" class="Argument">β</a> <a id="12740" class="Symbol">=</a> <a id="12742" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12746" class="Symbol">_}</a> <a id="12749" class="Symbol">=</a> <a id="12751" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12758" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12768" class="Symbol">{</a><a id="12769" class="Argument">α</a> <a id="12771" class="Symbol">=</a> <a id="12773" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12777" class="Symbol">_}</a> <a id="12780" class="Symbol">{</a><a id="12781" class="Argument">β</a> <a id="12783" class="Symbol">=</a> <a id="12785" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12789" class="Symbol">}</a>  <a id="12792" class="Symbol">=</a> <a id="12794" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12801" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12811" class="Symbol">{</a><a id="12812" class="Argument">α</a> <a id="12814" class="Symbol">=</a> <a id="12816" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12820" class="Symbol">_}</a> <a id="12823" class="Symbol">{</a><a id="12824" class="Argument">β</a> <a id="12826" class="Symbol">=</a> <a id="12828" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12832" class="Symbol">_}</a> <a id="12835" class="Symbol">=</a> <a id="12837" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12844" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12854" class="Symbol">{</a><a id="12855" class="Argument">α</a> <a id="12857" class="Symbol">=</a> <a id="12859" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12863" class="Symbol">_}</a> <a id="12866" class="Symbol">{</a><a id="12867" class="Argument">β</a> <a id="12869" class="Symbol">=</a> <a id="12871" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12875" class="Symbol">_}</a> <a id="12878" class="Symbol">=</a> <a id="12880" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12887" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12897" class="Symbol">{</a><a id="12898" class="Argument">α</a> <a id="12900" class="Symbol">=</a> <a id="12902" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12906" class="Symbol">_}</a> <a id="12909" class="Symbol">{</a><a id="12910" class="Argument">β</a> <a id="12912" class="Symbol">=</a> <a id="12914" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="12918" class="Symbol">}</a>  <a id="12921" class="Symbol">=</a> <a id="12923" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12930" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12940" class="Symbol">{</a><a id="12941" class="Argument">α</a> <a id="12943" class="Symbol">=</a> <a id="12945" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12949" class="Symbol">_}</a> <a id="12952" class="Symbol">{</a><a id="12953" class="Argument">β</a> <a id="12955" class="Symbol">=</a> <a id="12957" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="12961" class="Symbol">_}</a> <a id="12964" class="Symbol">=</a> <a id="12966" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="12973" href="Veblen.Multinary.html#12583" class="Function">φ-α-β-suc</a> <a id="12983" class="Symbol">{</a><a id="12984" class="Argument">α</a> <a id="12986" class="Symbol">=</a> <a id="12988" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="12992" class="Symbol">_}</a> <a id="12995" class="Symbol">{</a><a id="12996" class="Argument">β</a> <a id="12998" class="Symbol">=</a> <a id="13000" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13004" class="Symbol">_}</a> <a id="13007" class="Symbol">=</a> <a id="13009" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

  <a id="QuaternaryVeblen.φ-α-β-lim"></a><a id="13017" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13027" class="Symbol">:</a> <a id="13029" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="13031" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="13033" href="Veblen.Basic.html#4152" class="Generalizable">β</a> <a id="13035" class="Symbol">(</a><a id="13036" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13040" href="Veblen.Basic.html#9427" class="Generalizable">h</a><a id="13041" class="Symbol">)</a> <a id="13043" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="13045" href="Veblen.Basic.html#11585" class="Function">jump</a> <a id="13050" class="Symbol">λ</a> <a id="13052" href="Veblen.Multinary.html#13052" class="Bound">δ</a> <a id="13054" class="Symbol">→</a> <a id="13056" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13060" class="Symbol">λ</a> <a id="13062" href="Veblen.Multinary.html#13062" class="Bound">n</a> <a id="13064" class="Symbol">→</a> <a id="13066" href="Veblen.Multinary.html#10869" class="Function">φ</a> <a id="13068" href="Veblen.Basic.html#4150" class="Generalizable">α</a> <a id="13070" href="Veblen.Basic.html#4152" class="Generalizable">β</a> <a id="13072" class="Symbol">(</a><a id="13073" href="Veblen.Basic.html#9427" class="Generalizable">h</a> <a id="13075" href="Veblen.Multinary.html#13062" class="Bound">n</a><a id="13076" class="Symbol">)</a> <a id="13078" href="Veblen.Multinary.html#13052" class="Bound">δ</a>
  <a id="13082" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13092" class="Symbol">{</a><a id="13093" class="Argument">α</a> <a id="13095" class="Symbol">=</a> <a id="13097" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13101" class="Symbol">}</a>  <a id="13104" class="Symbol">{</a><a id="13105" class="Argument">β</a> <a id="13107" class="Symbol">=</a> <a id="13109" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13113" class="Symbol">}</a>  <a id="13116" class="Symbol">=</a> <a id="13118" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13125" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13135" class="Symbol">{</a><a id="13136" class="Argument">α</a> <a id="13138" class="Symbol">=</a> <a id="13140" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13144" class="Symbol">}</a>  <a id="13147" class="Symbol">{</a><a id="13148" class="Argument">β</a> <a id="13150" class="Symbol">=</a> <a id="13152" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13156" class="Symbol">_}</a> <a id="13159" class="Symbol">=</a> <a id="13161" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13168" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13178" class="Symbol">{</a><a id="13179" class="Argument">α</a> <a id="13181" class="Symbol">=</a> <a id="13183" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13187" class="Symbol">}</a>  <a id="13190" class="Symbol">{</a><a id="13191" class="Argument">β</a> <a id="13193" class="Symbol">=</a> <a id="13195" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13199" class="Symbol">_}</a> <a id="13202" class="Symbol">=</a> <a id="13204" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13211" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13221" class="Symbol">{</a><a id="13222" class="Argument">α</a> <a id="13224" class="Symbol">=</a> <a id="13226" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13230" class="Symbol">_}</a> <a id="13233" class="Symbol">{</a><a id="13234" class="Argument">β</a> <a id="13236" class="Symbol">=</a> <a id="13238" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13242" class="Symbol">}</a>  <a id="13245" class="Symbol">=</a> <a id="13247" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13254" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13264" class="Symbol">{</a><a id="13265" class="Argument">α</a> <a id="13267" class="Symbol">=</a> <a id="13269" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13273" class="Symbol">_}</a> <a id="13276" class="Symbol">{</a><a id="13277" class="Argument">β</a> <a id="13279" class="Symbol">=</a> <a id="13281" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13285" class="Symbol">_}</a> <a id="13288" class="Symbol">=</a> <a id="13290" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13297" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13307" class="Symbol">{</a><a id="13308" class="Argument">α</a> <a id="13310" class="Symbol">=</a> <a id="13312" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13316" class="Symbol">_}</a> <a id="13319" class="Symbol">{</a><a id="13320" class="Argument">β</a> <a id="13322" class="Symbol">=</a> <a id="13324" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13328" class="Symbol">_}</a> <a id="13331" class="Symbol">=</a> <a id="13333" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13340" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13350" class="Symbol">{</a><a id="13351" class="Argument">α</a> <a id="13353" class="Symbol">=</a> <a id="13355" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13359" class="Symbol">_}</a> <a id="13362" class="Symbol">{</a><a id="13363" class="Argument">β</a> <a id="13365" class="Symbol">=</a> <a id="13367" href="Veblen.Basic.html#3261" class="InductiveConstructor">zero</a><a id="13371" class="Symbol">}</a>  <a id="13374" class="Symbol">=</a> <a id="13376" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13383" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13393" class="Symbol">{</a><a id="13394" class="Argument">α</a> <a id="13396" class="Symbol">=</a> <a id="13398" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13402" class="Symbol">_}</a> <a id="13405" class="Symbol">{</a><a id="13406" class="Argument">β</a> <a id="13408" class="Symbol">=</a> <a id="13410" href="Veblen.Basic.html#3274" class="InductiveConstructor">suc</a> <a id="13414" class="Symbol">_}</a> <a id="13417" class="Symbol">=</a> <a id="13419" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
  <a id="13426" href="Veblen.Multinary.html#13017" class="Function">φ-α-β-lim</a> <a id="13436" class="Symbol">{</a><a id="13437" class="Argument">α</a> <a id="13439" class="Symbol">=</a> <a id="13441" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13445" class="Symbol">_}</a> <a id="13448" class="Symbol">{</a><a id="13449" class="Argument">β</a> <a id="13451" class="Symbol">=</a> <a id="13453" href="Veblen.Basic.html#3293" class="InductiveConstructor">lim</a> <a id="13457" class="Symbol">_}</a> <a id="13460" class="Symbol">=</a> <a id="13462" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
**例** 一个很大的大数:

$$
\text{oom}_2 := f_{φ_{Γ_0,0,0}\kern{0.17em}(0)}(99)
$$

<pre class="Agda"><a id="oom₂"></a><a id="13555" href="Veblen.Multinary.html#13555" class="Function">oom₂</a> <a id="13560" class="Symbol">=</a> <a id="13562" href="Veblen.Basic.html#5665" class="Function">FGH.f</a> <a id="13568" class="Symbol">(</a><a id="13569" href="Veblen.Multinary.html#10869" class="Function">QuaternaryVeblen.φ</a> <a id="13588" class="Symbol">(</a><a id="13589" href="Veblen.Multinary.html#4682" class="Function">BinaryVeblen.Γ</a> <a id="13604" class="Number">0</a><a id="13605" class="Symbol">)</a> <a id="13607" class="Number">0</a> <a id="13609" class="Number">0</a> <a id="13611" class="Number">0</a><a id="13612" class="Symbol">)</a> <a id="13614" class="Number">99</a>
</pre>