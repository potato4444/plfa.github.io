---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations/
---

<pre class="Agda">{% raw %}<a id="123" class="Keyword">module</a> <a id="130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="145" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

<pre class="Agda">{% raw %}<a id="326" class="Keyword">import</a> <a id="333" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="371" class="Symbol">as</a> <a id="374" class="Module">Eq</a>
<a id="377" class="Keyword">open</a> <a id="382" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="385" class="Keyword">using</a> <a id="391" class="Symbol">(</a><a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="395" class="Symbol">;</a> <a id="397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="407" class="Symbol">;</a> <a id="409" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="412" class="Symbol">)</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a><a id="442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="443" class="Symbol">;</a> <a id="445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="449" class="Symbol">;</a> <a id="451" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="459" class="Symbol">;</a> <a id="461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="464" class="Symbol">;</a> <a id="466" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="469" class="Symbol">)</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a><a id="510" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="516" class="Symbol">;</a> <a id="518" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="523" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1200" class="Keyword">data</a> <a id="_≤_"></a><a id="1205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1213" class="Symbol">→</a> <a id="1215" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1217" class="Symbol">→</a> <a id="1219" class="PrimitiveType">Set</a> <a id="1223" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="1231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="1235" class="Symbol">:</a> <a id="1237" class="Symbol">∀</a> <a id="1239" class="Symbol">{</a><a id="1240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1240" class="Bound">m</a> <a id="1242" class="Symbol">:</a> <a id="1244" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1245" class="Symbol">}</a> <a id="1247" class="Symbol">→</a> <a id="1249" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1240" class="Bound">m</a>
  <a id="_≤_.s≤s"></a><a id="1260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="1264" class="Symbol">:</a> <a id="1266" class="Symbol">∀</a> <a id="1268" class="Symbol">{</a><a id="1269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1276" class="Symbol">}</a> <a id="1278" class="Symbol">→</a> <a id="1280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1286" class="Symbol">→</a> <a id="1288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `zero ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2354" class="Function">_</a> <a id="2356" class="Symbol">:</a> <a id="2358" class="Number">2</a> <a id="2360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="2362" class="Number">4</a>
<a id="2364" class="Symbol">_</a> <a id="2366" class="Symbol">=</a> <a id="2368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2372" class="Symbol">(</a><a id="2373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a><a id="2380" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `zero ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that
`m ≤ n`, we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving
both `m` and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3372" class="Function">_</a> <a id="3374" class="Symbol">:</a> <a id="3376" class="Number">2</a> <a id="3378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="3380" class="Number">4</a>
<a id="3382" class="Symbol">_</a> <a id="3384" class="Symbol">=</a> <a id="3386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3390" class="Symbol">{</a><a id="3391" class="Number">1</a><a id="3392" class="Symbol">}</a> <a id="3394" class="Symbol">{</a><a id="3395" class="Number">3</a><a id="3396" class="Symbol">}</a> <a id="3398" class="Symbol">(</a><a id="3399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3403" class="Symbol">{</a><a id="3404" class="Number">0</a><a id="3405" class="Symbol">}</a> <a id="3407" class="Symbol">{</a><a id="3408" class="Number">2</a><a id="3409" class="Symbol">}</a> <a id="3411" class="Symbol">(</a><a id="3412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="3416" class="Symbol">{</a><a id="3417" class="Number">2</a><a id="3418" class="Symbol">}))</a>{% endraw %}</pre>


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="3516" class="Keyword">infix</a> <a id="3522" class="Number">4</a> <a id="3524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md %}).


## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="5710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5717" class="Symbol">:</a> <a id="5719" class="Symbol">∀</a> <a id="5721" class="Symbol">{</a><a id="5722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a> <a id="5724" class="Symbol">:</a> <a id="5726" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5727" class="Symbol">}</a> <a id="5729" class="Symbol">→</a> <a id="5731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a> <a id="5733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="5735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a>
<a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5744" class="Symbol">{</a><a id="5745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="5749" class="Symbol">}</a> <a id="5751" class="Symbol">=</a> <a id="5753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="5757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5764" class="Symbol">{</a><a id="5765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5769" class="Bound">n</a><a id="5770" class="Symbol">}</a> <a id="5772" class="Symbol">=</a> <a id="5774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="5778" class="Symbol">(</a><a id="5779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5786" class="Symbol">{</a><a id="5787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5769" class="Bound">n</a><a id="5788" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a> <a id="6376" class="Symbol">:</a> <a id="6378" class="Symbol">∀</a> <a id="6380" class="Symbol">{</a><a id="6381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6381" class="Bound">m</a> <a id="6383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6383" class="Bound">n</a> <a id="6385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6385" class="Bound">p</a> <a id="6387" class="Symbol">:</a> <a id="6389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6390" class="Symbol">}</a> <a id="6392" class="Symbol">→</a> <a id="6394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6381" class="Bound">m</a> <a id="6396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6383" class="Bound">n</a> <a id="6400" class="Symbol">→</a> <a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6383" class="Bound">n</a> <a id="6404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6385" class="Bound">p</a> <a id="6408" class="Symbol">→</a> <a id="6410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6381" class="Bound">m</a> <a id="6412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6385" class="Bound">p</a>
<a id="6416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a> <a id="6424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="6428" class="Symbol">_</a> <a id="6430" class="Symbol">=</a> <a id="6432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="6436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a> <a id="6444" class="Symbol">(</a><a id="6445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6449" class="Bound">m≤n</a><a id="6452" class="Symbol">)</a> <a id="6454" class="Symbol">(</a><a id="6455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6459" class="Bound">n≤p</a><a id="6462" class="Symbol">)</a> <a id="6464" class="Symbol">=</a> <a id="6466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6470" class="Symbol">(</a><a id="6471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a> <a id="6479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6449" class="Bound">m≤n</a> <a id="6483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6459" class="Bound">n≤p</a><a id="6486" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="7565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7565" class="Function">≤-trans′</a> <a id="7574" class="Symbol">:</a> <a id="7576" class="Symbol">∀</a> <a id="7578" class="Symbol">(</a><a id="7579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7579" class="Bound">m</a> <a id="7581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7581" class="Bound">n</a> <a id="7583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7583" class="Bound">p</a> <a id="7585" class="Symbol">:</a> <a id="7587" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7588" class="Symbol">)</a> <a id="7590" class="Symbol">→</a> <a id="7592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7579" class="Bound">m</a> <a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7581" class="Bound">n</a> <a id="7598" class="Symbol">→</a> <a id="7600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7581" class="Bound">n</a> <a id="7602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7583" class="Bound">p</a> <a id="7606" class="Symbol">→</a> <a id="7608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7579" class="Bound">m</a> <a id="7610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7583" class="Bound">p</a>
<a id="7614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7565" class="Function">≤-trans′</a> <a id="7623" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7628" class="Bound">n</a> <a id="7630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7630" class="Bound">p</a> <a id="7632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="7636" class="Symbol">_</a> <a id="7638" class="Symbol">=</a> <a id="7640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="7644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7565" class="Function">≤-trans′</a> <a id="7653" class="Symbol">(</a><a id="7654" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7658" class="Bound">m</a><a id="7659" class="Symbol">)</a> <a id="7661" class="Symbol">(</a><a id="7662" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7666" class="Bound">n</a><a id="7667" class="Symbol">)</a> <a id="7669" class="Symbol">(</a><a id="7670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7674" class="Bound">p</a><a id="7675" class="Symbol">)</a> <a id="7677" class="Symbol">(</a><a id="7678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7682" class="Bound">m≤n</a><a id="7685" class="Symbol">)</a> <a id="7687" class="Symbol">(</a><a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7692" class="Bound">n≤p</a><a id="7695" class="Symbol">)</a> <a id="7697" class="Symbol">=</a> <a id="7699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7703" class="Symbol">(</a><a id="7704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7565" class="Function">≤-trans′</a> <a id="7713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7658" class="Bound">m</a> <a id="7715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7666" class="Bound">n</a> <a id="7717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7674" class="Bound">p</a> <a id="7719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7682" class="Bound">m≤n</a> <a id="7723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7692" class="Bound">n≤p</a><a id="7726" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="8484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8484" class="Function">≤-antisym</a> <a id="8494" class="Symbol">:</a> <a id="8496" class="Symbol">∀</a> <a id="8498" class="Symbol">{</a><a id="8499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8499" class="Bound">m</a> <a id="8501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8501" class="Bound">n</a> <a id="8503" class="Symbol">:</a> <a id="8505" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8506" class="Symbol">}</a> <a id="8508" class="Symbol">→</a> <a id="8510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8499" class="Bound">m</a> <a id="8512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8501" class="Bound">n</a> <a id="8516" class="Symbol">→</a> <a id="8518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8501" class="Bound">n</a> <a id="8520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8499" class="Bound">m</a> <a id="8524" class="Symbol">→</a> <a id="8526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8499" class="Bound">m</a> <a id="8528" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8501" class="Bound">n</a>
<a id="8532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8484" class="Function">≤-antisym</a> <a id="8542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8550" class="Symbol">=</a> <a id="8552" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="8557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8484" class="Function">≤-antisym</a> <a id="8567" class="Symbol">(</a><a id="8568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8572" class="Bound">m≤n</a><a id="8575" class="Symbol">)</a> <a id="8577" class="Symbol">(</a><a id="8578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8582" class="Bound">n≤m</a><a id="8585" class="Symbol">)</a> <a id="8587" class="Symbol">=</a> <a id="8589" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="8594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8598" class="Symbol">(</a><a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8484" class="Function">≤-antisym</a> <a id="8609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8572" class="Bound">m≤n</a> <a id="8613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8582" class="Bound">n≤m</a><a id="8616" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.

### Exercise (≤-antisym-cases)

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="9668" class="Keyword">data</a> <a id="Total"></a><a id="9673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="9679" class="Symbol">(</a><a id="9680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9680" class="Bound">m</a> <a id="9682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9682" class="Bound">n</a> <a id="9684" class="Symbol">:</a> <a id="9686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9687" class="Symbol">)</a> <a id="9689" class="Symbol">:</a> <a id="9691" class="PrimitiveType">Set</a> <a id="9695" class="Keyword">where</a>
  <a id="Total.forward"></a><a id="9703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="9711" class="Symbol">:</a> <a id="9713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9680" class="Bound">m</a> <a id="9715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9682" class="Bound">n</a> <a id="9719" class="Symbol">→</a> <a id="9721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="9727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9680" class="Bound">m</a> <a id="9729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9682" class="Bound">n</a>
  <a id="Total.flipped"></a><a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="9741" class="Symbol">:</a> <a id="9743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9682" class="Bound">n</a> <a id="9745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9680" class="Bound">m</a> <a id="9749" class="Symbol">→</a> <a id="9751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="9757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9680" class="Bound">m</a> <a id="9759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9682" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="10078" class="Keyword">data</a> <a id="Total′"></a><a id="10083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10083" class="Datatype">Total′</a> <a id="10090" class="Symbol">:</a> <a id="10092" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10094" class="Symbol">→</a> <a id="10096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10098" class="Symbol">→</a> <a id="10100" class="PrimitiveType">Set</a> <a id="10104" class="Keyword">where</a>
  <a id="Total′.forward′"></a><a id="10112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10112" class="InductiveConstructor">forward′</a> <a id="10121" class="Symbol">:</a> <a id="10123" class="Symbol">∀</a> <a id="10125" class="Symbol">{</a><a id="10126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10126" class="Bound">m</a> <a id="10128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10128" class="Bound">n</a> <a id="10130" class="Symbol">:</a> <a id="10132" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10133" class="Symbol">}</a> <a id="10135" class="Symbol">→</a> <a id="10137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10126" class="Bound">m</a> <a id="10139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10128" class="Bound">n</a> <a id="10143" class="Symbol">→</a> <a id="10145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10083" class="Datatype">Total′</a> <a id="10152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10126" class="Bound">m</a> <a id="10154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10128" class="Bound">n</a>
  <a id="Total′.flipped′"></a><a id="10158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10158" class="InductiveConstructor">flipped′</a> <a id="10167" class="Symbol">:</a> <a id="10169" class="Symbol">∀</a> <a id="10171" class="Symbol">{</a><a id="10172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10172" class="Bound">m</a> <a id="10174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10174" class="Bound">n</a> <a id="10176" class="Symbol">:</a> <a id="10178" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10179" class="Symbol">}</a> <a id="10181" class="Symbol">→</a> <a id="10183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10174" class="Bound">n</a> <a id="10185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10172" class="Bound">m</a> <a id="10189" class="Symbol">→</a> <a id="10191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10083" class="Datatype">Total′</a> <a id="10198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10172" class="Bound">m</a> <a id="10200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10174" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="10740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10740" class="Function">≤-total</a> <a id="10748" class="Symbol">:</a> <a id="10750" class="Symbol">∀</a> <a id="10752" class="Symbol">(</a><a id="10753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10753" class="Bound">m</a> <a id="10755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10755" class="Bound">n</a> <a id="10757" class="Symbol">:</a> <a id="10759" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10760" class="Symbol">)</a> <a id="10762" class="Symbol">→</a> <a id="10764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="10770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10753" class="Bound">m</a> <a id="10772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10755" class="Bound">n</a>
<a id="10774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10740" class="Function">≤-total</a> <a id="10782" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="10790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10790" class="Bound">n</a>                         <a id="10816" class="Symbol">=</a>  <a id="10819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="10827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10740" class="Function">≤-total</a> <a id="10839" class="Symbol">(</a><a id="10840" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10844" class="Bound">m</a><a id="10845" class="Symbol">)</a> <a id="10847" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="10873" class="Symbol">=</a>  <a id="10876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="10884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10740" class="Function">≤-total</a> <a id="10896" class="Symbol">(</a><a id="10897" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10901" class="Bound">m</a><a id="10902" class="Symbol">)</a> <a id="10904" class="Symbol">(</a><a id="10905" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10909" class="Bound">n</a><a id="10910" class="Symbol">)</a> <a id="10912" class="Keyword">with</a> <a id="10917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10740" class="Function">≤-total</a> <a id="10925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10901" class="Bound">m</a> <a id="10927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10909" class="Bound">n</a>
<a id="10929" class="Symbol">...</a>                        <a id="10956" class="Symbol">|</a> <a id="10958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="10966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10966" class="Bound">m≤n</a>  <a id="10971" class="Symbol">=</a>  <a id="10974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="10982" class="Symbol">(</a><a id="10983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="10987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10966" class="Bound">m≤n</a><a id="10990" class="Symbol">)</a>
<a id="10992" class="Symbol">...</a>                        <a id="11019" class="Symbol">|</a> <a id="11021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="11029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11029" class="Bound">n≤m</a>  <a id="11034" class="Symbol">=</a>  <a id="11037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="11045" class="Symbol">(</a><a id="11046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="11050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11029" class="Bound">n≤m</a><a id="11053" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="12561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12561" class="Function">≤-total′</a> <a id="12570" class="Symbol">:</a> <a id="12572" class="Symbol">∀</a> <a id="12574" class="Symbol">(</a><a id="12575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12575" class="Bound">m</a> <a id="12577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12577" class="Bound">n</a> <a id="12579" class="Symbol">:</a> <a id="12581" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12582" class="Symbol">)</a> <a id="12584" class="Symbol">→</a> <a id="12586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="12592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12575" class="Bound">m</a> <a id="12594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12577" class="Bound">n</a>
<a id="12596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12561" class="Function">≤-total′</a> <a id="12605" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12613" class="Bound">n</a>        <a id="12622" class="Symbol">=</a>  <a id="12625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="12633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12561" class="Function">≤-total′</a> <a id="12646" class="Symbol">(</a><a id="12647" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12651" class="Bound">m</a><a id="12652" class="Symbol">)</a> <a id="12654" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="12663" class="Symbol">=</a>  <a id="12666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="12674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12561" class="Function">≤-total′</a> <a id="12687" class="Symbol">(</a><a id="12688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12692" class="Bound">m</a><a id="12693" class="Symbol">)</a> <a id="12695" class="Symbol">(</a><a id="12696" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12700" class="Bound">n</a><a id="12701" class="Symbol">)</a>  <a id="12704" class="Symbol">=</a>  <a id="12707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12739" class="Function">helper</a> <a id="12714" class="Symbol">(</a><a id="12715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12561" class="Function">≤-total′</a> <a id="12724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12692" class="Bound">m</a> <a id="12726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12700" class="Bound">n</a><a id="12727" class="Symbol">)</a>
  <a id="12731" class="Keyword">where</a>
  <a id="12739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12739" class="Function">helper</a> <a id="12746" class="Symbol">:</a> <a id="12748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="12754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12692" class="Bound">m</a> <a id="12756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12700" class="Bound">n</a> <a id="12758" class="Symbol">→</a> <a id="12760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="12766" class="Symbol">(</a><a id="12767" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12692" class="Bound">m</a><a id="12772" class="Symbol">)</a> <a id="12774" class="Symbol">(</a><a id="12775" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12700" class="Bound">n</a><a id="12780" class="Symbol">)</a>
  <a id="12784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12739" class="Function">helper</a> <a id="12791" class="Symbol">(</a><a id="12792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="12800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12800" class="Bound">m≤n</a><a id="12803" class="Symbol">)</a>  <a id="12806" class="Symbol">=</a>  <a id="12809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="12817" class="Symbol">(</a><a id="12818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12800" class="Bound">m≤n</a><a id="12825" class="Symbol">)</a>
  <a id="12829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12739" class="Function">helper</a> <a id="12836" class="Symbol">(</a><a id="12837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="12845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12845" class="Bound">n≤m</a><a id="12848" class="Symbol">)</a>  <a id="12851" class="Symbol">=</a>  <a id="12854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="12862" class="Symbol">(</a><a id="12863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12845" class="Bound">n≤m</a><a id="12870" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="13508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13508" class="Function">≤-total″</a> <a id="13517" class="Symbol">:</a> <a id="13519" class="Symbol">∀</a> <a id="13521" class="Symbol">(</a><a id="13522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13522" class="Bound">m</a> <a id="13524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13524" class="Bound">n</a> <a id="13526" class="Symbol">:</a> <a id="13528" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13529" class="Symbol">)</a> <a id="13531" class="Symbol">→</a> <a id="13533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9673" class="Datatype">Total</a> <a id="13539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13522" class="Bound">m</a> <a id="13541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13524" class="Bound">n</a>
<a id="13543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13508" class="Function">≤-total″</a> <a id="13552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13552" class="Bound">m</a>       <a id="13560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="13586" class="Symbol">=</a>  <a id="13589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="13597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13508" class="Function">≤-total″</a> <a id="13610" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13618" class="Symbol">(</a><a id="13619" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13623" class="Bound">n</a><a id="13624" class="Symbol">)</a>                   <a id="13644" class="Symbol">=</a>  <a id="13647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="13655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13508" class="Function">≤-total″</a> <a id="13668" class="Symbol">(</a><a id="13669" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13673" class="Bound">m</a><a id="13674" class="Symbol">)</a> <a id="13676" class="Symbol">(</a><a id="13677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13681" class="Bound">n</a><a id="13682" class="Symbol">)</a> <a id="13684" class="Keyword">with</a> <a id="13689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13508" class="Function">≤-total″</a> <a id="13698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13673" class="Bound">m</a> <a id="13700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13681" class="Bound">n</a>
<a id="13702" class="Symbol">...</a>                        <a id="13729" class="Symbol">|</a> <a id="13731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="13739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13739" class="Bound">m≤n</a>   <a id="13745" class="Symbol">=</a>  <a id="13748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9703" class="InductiveConstructor">forward</a> <a id="13756" class="Symbol">(</a><a id="13757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13739" class="Bound">m≤n</a><a id="13764" class="Symbol">)</a>
<a id="13766" class="Symbol">...</a>                        <a id="13793" class="Symbol">|</a> <a id="13795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="13803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13803" class="Bound">n≤m</a>   <a id="13809" class="Symbol">=</a>  <a id="13812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9733" class="InductiveConstructor">flipped</a> <a id="13820" class="Symbol">(</a><a id="13821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13803" class="Bound">n≤m</a><a id="13828" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="14432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="14442" class="Symbol">:</a> <a id="14444" class="Symbol">∀</a> <a id="14446" class="Symbol">(</a><a id="14447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14447" class="Bound">m</a> <a id="14449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14449" class="Bound">p</a> <a id="14451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14451" class="Bound">q</a> <a id="14453" class="Symbol">:</a> <a id="14455" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14456" class="Symbol">)</a> <a id="14458" class="Symbol">→</a> <a id="14460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14449" class="Bound">p</a> <a id="14462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14451" class="Bound">q</a> <a id="14466" class="Symbol">→</a> <a id="14468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14447" class="Bound">m</a> <a id="14470" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14449" class="Bound">p</a> <a id="14474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14447" class="Bound">m</a> <a id="14478" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14451" class="Bound">q</a>
<a id="14482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="14492" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14500" class="Bound">p</a> <a id="14502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14502" class="Bound">q</a> <a id="14504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14504" class="Bound">p≤q</a>  <a id="14509" class="Symbol">=</a>  <a id="14512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14504" class="Bound">p≤q</a>
<a id="14516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="14526" class="Symbol">(</a><a id="14527" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14531" class="Bound">m</a><a id="14532" class="Symbol">)</a> <a id="14534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14534" class="Bound">p</a> <a id="14536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14536" class="Bound">q</a> <a id="14538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14538" class="Bound">p≤q</a>  <a id="14543" class="Symbol">=</a>  <a id="14546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="14550" class="Symbol">(</a><a id="14551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="14561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14531" class="Bound">m</a> <a id="14563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14534" class="Bound">p</a> <a id="14565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14536" class="Bound">q</a> <a id="14567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14538" class="Bound">p≤q</a><a id="14570" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="15226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15226" class="Function">+-monoˡ-≤</a> <a id="15236" class="Symbol">:</a> <a id="15238" class="Symbol">∀</a> <a id="15240" class="Symbol">(</a><a id="15241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15241" class="Bound">m</a> <a id="15243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15243" class="Bound">n</a> <a id="15245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15245" class="Bound">p</a> <a id="15247" class="Symbol">:</a> <a id="15249" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15250" class="Symbol">)</a> <a id="15252" class="Symbol">→</a> <a id="15254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15241" class="Bound">m</a> <a id="15256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15243" class="Bound">n</a> <a id="15260" class="Symbol">→</a> <a id="15262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15241" class="Bound">m</a> <a id="15264" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15245" class="Bound">p</a> <a id="15268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15243" class="Bound">n</a> <a id="15272" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15245" class="Bound">p</a>
<a id="15276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15226" class="Function">+-monoˡ-≤</a> <a id="15286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15286" class="Bound">m</a> <a id="15288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15288" class="Bound">n</a> <a id="15290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15290" class="Bound">p</a> <a id="15292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15292" class="Bound">m≤n</a> <a id="15296" class="Keyword">rewrite</a> <a id="15304" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15286" class="Bound">m</a> <a id="15313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15290" class="Bound">p</a> <a id="15315" class="Symbol">|</a> <a id="15317" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15288" class="Bound">n</a> <a id="15326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15290" class="Bound">p</a> <a id="15328" class="Symbol">=</a> <a id="15330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="15340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15290" class="Bound">p</a> <a id="15342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15286" class="Bound">m</a> <a id="15344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15288" class="Bound">n</a> <a id="15346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15292" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="15560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15560" class="Function">+-mono-≤</a> <a id="15569" class="Symbol">:</a> <a id="15571" class="Symbol">∀</a> <a id="15573" class="Symbol">(</a><a id="15574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15574" class="Bound">m</a> <a id="15576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15576" class="Bound">n</a> <a id="15578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15578" class="Bound">p</a> <a id="15580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15580" class="Bound">q</a> <a id="15582" class="Symbol">:</a> <a id="15584" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15585" class="Symbol">)</a> <a id="15587" class="Symbol">→</a> <a id="15589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15574" class="Bound">m</a> <a id="15591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15576" class="Bound">n</a> <a id="15595" class="Symbol">→</a> <a id="15597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15578" class="Bound">p</a> <a id="15599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15580" class="Bound">q</a> <a id="15603" class="Symbol">→</a> <a id="15605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15574" class="Bound">m</a> <a id="15607" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15578" class="Bound">p</a> <a id="15611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15576" class="Bound">n</a> <a id="15615" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15580" class="Bound">q</a>
<a id="15619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15560" class="Function">+-mono-≤</a> <a id="15628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15628" class="Bound">m</a> <a id="15630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15630" class="Bound">n</a> <a id="15632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15632" class="Bound">p</a> <a id="15634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15634" class="Bound">q</a> <a id="15636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15636" class="Bound">m≤n</a> <a id="15640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Bound">p≤q</a> <a id="15644" class="Symbol">=</a> <a id="15646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a> <a id="15654" class="Symbol">(</a><a id="15655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15226" class="Function">+-monoˡ-≤</a> <a id="15665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15628" class="Bound">m</a> <a id="15667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15630" class="Bound">n</a> <a id="15669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15632" class="Bound">p</a> <a id="15671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15636" class="Bound">m≤n</a><a id="15674" class="Symbol">)</a> <a id="15676" class="Symbol">(</a><a id="15677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14432" class="Function">+-monoʳ-≤</a> <a id="15687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15630" class="Bound">n</a> <a id="15689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15632" class="Bound">p</a> <a id="15691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15634" class="Bound">q</a> <a id="15693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Bound">p≤q</a><a id="15696" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.

### Exercise (stretch, `≤-reasoning`)

The proof of monotonicity (and the associated lemmas) can be written
in a more readable form by using an anologue of our notation for
`≡-reasoning`.  Read ahead to chapter [Equality]({{ site.baseurl }}{% link out/plfa/Equality.md %}) to
see how `≡-reasoning` is defined, define `≤-reasoning` analogously,
and use it to write out an alternative proof that addition is
monotonic with regard to inequality.


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="16463" class="Keyword">infix</a> <a id="16469" class="Number">4</a> <a id="16471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16481" class="Datatype Operator">_&lt;_</a>

<a id="16476" class="Keyword">data</a> <a id="_&lt;_"></a><a id="16481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16481" class="Datatype Operator">_&lt;_</a> <a id="16485" class="Symbol">:</a> <a id="16487" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16489" class="Symbol">→</a> <a id="16491" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16493" class="Symbol">→</a> <a id="16495" class="PrimitiveType">Set</a> <a id="16499" class="Keyword">where</a>
  <a id="_&lt;_.z&lt;s"></a><a id="16507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16507" class="InductiveConstructor">z&lt;s</a> <a id="16511" class="Symbol">:</a> <a id="16513" class="Symbol">∀</a> <a id="16515" class="Symbol">{</a><a id="16516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16516" class="Bound">n</a> <a id="16518" class="Symbol">:</a> <a id="16520" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16521" class="Symbol">}</a> <a id="16523" class="Symbol">→</a> <a id="16525" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16481" class="Datatype Operator">&lt;</a> <a id="16532" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16516" class="Bound">n</a>
  <a id="_&lt;_.s&lt;s"></a><a id="16540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16540" class="InductiveConstructor">s&lt;s</a> <a id="16544" class="Symbol">:</a> <a id="16546" class="Symbol">∀</a> <a id="16548" class="Symbol">{</a><a id="16549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16549" class="Bound">m</a> <a id="16551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16551" class="Bound">n</a> <a id="16553" class="Symbol">:</a> <a id="16555" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16556" class="Symbol">}</a> <a id="16558" class="Symbol">→</a> <a id="16560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16549" class="Bound">m</a> <a id="16562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16481" class="Datatype Operator">&lt;</a> <a id="16564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16551" class="Bound">n</a> <a id="16566" class="Symbol">→</a> <a id="16568" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16549" class="Bound">m</a> <a id="16574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16481" class="Datatype Operator">&lt;</a> <a id="16576" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16551" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
to the chapter that introduces [negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`
This only involves two relations, as we define `m > n` to
be the same as `n < m`. You will need a suitable data declaration,
similar to that used for totality.  (We will show that the three cases
are exclusive after [negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}) is introduced.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are *binary relations*, while even and odd are
*unary relations*, sometimes called *predicates*.
<pre class="Agda">{% raw %}<a id="18965" class="Keyword">data</a> <a id="even"></a><a id="18970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="18975" class="Symbol">:</a> <a id="18977" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18979" class="Symbol">→</a> <a id="18981" class="PrimitiveType">Set</a>
<a id="18985" class="Keyword">data</a> <a id="odd"></a><a id="18990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a>  <a id="18995" class="Symbol">:</a> <a id="18997" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18999" class="Symbol">→</a> <a id="19001" class="PrimitiveType">Set</a>

<a id="19006" class="Keyword">data</a> <a id="19011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="19016" class="Keyword">where</a>
  <a id="even.zero"></a><a id="19024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19024" class="InductiveConstructor">zero</a> <a id="19029" class="Symbol">:</a> <a id="19031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="19036" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="even.suc"></a><a id="19043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19043" class="InductiveConstructor">suc</a>  <a id="19048" class="Symbol">:</a> <a id="19050" class="Symbol">∀</a> <a id="19052" class="Symbol">{</a><a id="19053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19053" class="Bound">n</a> <a id="19055" class="Symbol">:</a> <a id="19057" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19058" class="Symbol">}</a> <a id="19060" class="Symbol">→</a> <a id="19062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a> <a id="19066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19053" class="Bound">n</a> <a id="19068" class="Symbol">→</a> <a id="19070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="19075" class="Symbol">(</a><a id="19076" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19053" class="Bound">n</a><a id="19081" class="Symbol">)</a>

<a id="19084" class="Keyword">data</a> <a id="19089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a> <a id="19093" class="Keyword">where</a>
  <a id="odd.suc"></a><a id="19101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19101" class="InductiveConstructor">suc</a>   <a id="19107" class="Symbol">:</a> <a id="19109" class="Symbol">∀</a> <a id="19111" class="Symbol">{</a><a id="19112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19112" class="Bound">n</a> <a id="19114" class="Symbol">:</a> <a id="19116" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19117" class="Symbol">}</a> <a id="19119" class="Symbol">→</a> <a id="19121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="19126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19112" class="Bound">n</a> <a id="19128" class="Symbol">→</a> <a id="19130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a> <a id="19134" class="Symbol">(</a><a id="19135" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19112" class="Bound">n</a><a id="19140" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of *overloaded* constructors,
that is, using the same name for different constructors depending on
the context.  Here `suc` means one of three constructors:

    suc : `ℕ → `ℕ
    suc : ∀ {n : ℕ} → odd n → even (suc n)
    suc : ∀ {n : ℕ} → even n → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="20268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20268" class="Function">e+e≡e</a> <a id="20274" class="Symbol">:</a> <a id="20276" class="Symbol">∀</a> <a id="20278" class="Symbol">{</a><a id="20279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20279" class="Bound">m</a> <a id="20281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20281" class="Bound">n</a> <a id="20283" class="Symbol">:</a> <a id="20285" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20286" class="Symbol">}</a> <a id="20288" class="Symbol">→</a> <a id="20290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="20295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20279" class="Bound">m</a> <a id="20297" class="Symbol">→</a> <a id="20299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="20304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20281" class="Bound">n</a> <a id="20306" class="Symbol">→</a> <a id="20308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="20313" class="Symbol">(</a><a id="20314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20279" class="Bound">m</a> <a id="20316" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20281" class="Bound">n</a><a id="20319" class="Symbol">)</a>
<a id="o+e≡o"></a><a id="20321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20321" class="Function">o+e≡o</a> <a id="20327" class="Symbol">:</a> <a id="20329" class="Symbol">∀</a> <a id="20331" class="Symbol">{</a><a id="20332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20332" class="Bound">m</a> <a id="20334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20334" class="Bound">n</a> <a id="20336" class="Symbol">:</a> <a id="20338" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20339" class="Symbol">}</a> <a id="20341" class="Symbol">→</a> <a id="20343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a>  <a id="20348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20332" class="Bound">m</a> <a id="20350" class="Symbol">→</a> <a id="20352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18970" class="Datatype">even</a> <a id="20357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20334" class="Bound">n</a> <a id="20359" class="Symbol">→</a> <a id="20361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18990" class="Datatype">odd</a>  <a id="20366" class="Symbol">(</a><a id="20367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20332" class="Bound">m</a> <a id="20369" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20334" class="Bound">n</a><a id="20372" class="Symbol">)</a>

<a id="20375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20268" class="Function">e+e≡e</a> <a id="20381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19024" class="InductiveConstructor">zero</a>     <a id="20390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20390" class="Bound">en</a>  <a id="20394" class="Symbol">=</a>  <a id="20397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20390" class="Bound">en</a>
<a id="20400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20268" class="Function">e+e≡e</a> <a id="20406" class="Symbol">(</a><a id="20407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19043" class="InductiveConstructor">suc</a> <a id="20411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20411" class="Bound">om</a><a id="20413" class="Symbol">)</a> <a id="20415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20415" class="Bound">en</a>  <a id="20419" class="Symbol">=</a>  <a id="20422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19043" class="InductiveConstructor">suc</a> <a id="20426" class="Symbol">(</a><a id="20427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20321" class="Function">o+e≡o</a> <a id="20433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20411" class="Bound">om</a> <a id="20436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20415" class="Bound">en</a><a id="20438" class="Symbol">)</a>

<a id="20441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20321" class="Function">o+e≡o</a> <a id="20447" class="Symbol">(</a><a id="20448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19101" class="InductiveConstructor">suc</a> <a id="20452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20452" class="Bound">em</a><a id="20454" class="Symbol">)</a> <a id="20456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20456" class="Bound">en</a>  <a id="20460" class="Symbol">=</a>  <a id="20463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19101" class="InductiveConstructor">suc</a> <a id="20467" class="Symbol">(</a><a id="20468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20268" class="Function">e+e≡e</a> <a id="20474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20452" class="Bound">em</a> <a id="20477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20456" class="Bound">en</a><a id="20479" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it is because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


<!--

## Formalising preorder

<pre class="Agda">{% raw %}<a id="21640" class="Keyword">record</a> <a id="IsPreorder"></a><a id="21647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21647" class="Record">IsPreorder</a> <a id="21658" class="Symbol">{</a><a id="21659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21659" class="Bound">A</a> <a id="21661" class="Symbol">:</a> <a id="21663" class="PrimitiveType">Set</a><a id="21666" class="Symbol">}</a> <a id="21668" class="Symbol">(</a><a id="21669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21669" class="Bound Operator">_≤_</a> <a id="21673" class="Symbol">:</a> <a id="21675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21659" class="Bound">A</a> <a id="21677" class="Symbol">→</a> <a id="21679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21659" class="Bound">A</a> <a id="21681" class="Symbol">→</a> <a id="21683" class="PrimitiveType">Set</a><a id="21686" class="Symbol">)</a> <a id="21688" class="Symbol">:</a> <a id="21690" class="PrimitiveType">Set</a> <a id="21694" class="Keyword">where</a>
  <a id="21702" class="Keyword">field</a>
    <a id="IsPreorder.reflexive"></a><a id="21712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21712" class="Field">reflexive</a> <a id="21722" class="Symbol">:</a> <a id="21724" class="Symbol">∀</a> <a id="21726" class="Symbol">{</a><a id="21727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21727" class="Bound">x</a> <a id="21729" class="Symbol">:</a> <a id="21731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21659" class="Bound">A</a><a id="21732" class="Symbol">}</a> <a id="21734" class="Symbol">→</a> <a id="21736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21727" class="Bound">x</a> <a id="21738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21669" class="Bound Operator">≤</a> <a id="21740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21727" class="Bound">x</a>
    <a id="IsPreorder.trans"></a><a id="21746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21746" class="Field">trans</a> <a id="21752" class="Symbol">:</a> <a id="21754" class="Symbol">∀</a> <a id="21756" class="Symbol">{</a><a id="21757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21757" class="Bound">x</a> <a id="21759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21759" class="Bound">y</a> <a id="21761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21761" class="Bound">z</a> <a id="21763" class="Symbol">:</a> <a id="21765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21659" class="Bound">A</a><a id="21766" class="Symbol">}</a> <a id="21768" class="Symbol">→</a> <a id="21770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21757" class="Bound">x</a> <a id="21772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21669" class="Bound Operator">≤</a> <a id="21774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21759" class="Bound">y</a> <a id="21776" class="Symbol">→</a> <a id="21778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21759" class="Bound">y</a> <a id="21780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21669" class="Bound Operator">≤</a> <a id="21782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21761" class="Bound">z</a> <a id="21784" class="Symbol">→</a> <a id="21786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21757" class="Bound">x</a> <a id="21788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21669" class="Bound Operator">≤</a> <a id="21790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21761" class="Bound">z</a>

<a id="IsPreorder-≤"></a><a id="21793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21793" class="Function">IsPreorder-≤</a> <a id="21806" class="Symbol">:</a> <a id="21808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21647" class="Record">IsPreorder</a> <a id="21819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>
<a id="21823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21793" class="Function">IsPreorder-≤</a> <a id="21836" class="Symbol">=</a>
  <a id="21840" class="Keyword">record</a>
    <a id="21851" class="Symbol">{</a> <a id="21853" class="Field">reflexive</a> <a id="21863" class="Symbol">=</a> <a id="21865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a>
    <a id="21876" class="Symbol">;</a> <a id="21878" class="Field">trans</a> <a id="21884" class="Symbol">=</a> <a id="21886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6368" class="Function">≤-trans</a>
    <a id="21898" class="Symbol">}</a>{% endraw %}</pre>

-->


## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22035" class="Keyword">import</a> <a id="22042" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="22051" class="Keyword">using</a> <a id="22057" class="Symbol">(</a><a id="22058" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="22061" class="Symbol">;</a> <a id="22063" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="22066" class="Symbol">;</a> <a id="22068" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="22071" class="Symbol">)</a>
<a id="22073" class="Keyword">import</a> <a id="22080" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22100" class="Keyword">using</a> <a id="22106" class="Symbol">(</a><a id="22107" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1902" class="Function">≤-refl</a><a id="22113" class="Symbol">;</a> <a id="22115" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2095" class="Function">≤-trans</a><a id="22122" class="Symbol">;</a> <a id="22124" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1952" class="Function">≤-antisym</a><a id="22133" class="Symbol">;</a> <a id="22135" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2207" class="Function">≤-total</a><a id="22142" class="Symbol">;</a>
                                  <a id="22178" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#11056" class="Function">+-monoʳ-≤</a><a id="22187" class="Symbol">;</a> <a id="22189" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10966" class="Function">+-monoˡ-≤</a><a id="22198" class="Symbol">;</a> <a id="22200" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10810" class="Function">+-mono-≤</a><a id="22208" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md %})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here
as well as taking as implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
