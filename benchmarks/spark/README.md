# SPARK / GNATprove track

A fourth language track alongside Dafny, Verus and Lean, using
[SPARK](https://www.adacore.com/about-spark) — the provable subset of Ada —
with `gnatprove` as the checker.

The task shape is the same one the benchmark defines: **spec → verified
code**. The specification is given and fixed; the model writes the body and
whatever proof annotations the body needs; the checker either discharges
every proof obligation or it does not.

This is a seed set, not a finished track. It is offered as a starting point
that someone else can extend, and everything about how it was built is
written down below so that extending it does not require guessing.

## Layout

```
benchmarks/spark/
  README.md                     this file
  template.yaml                 the section template, as for the other languages
  spark_tasks.jsonl             all tasks, one JSON object per line
  numpy_simple/
    Readme.md
    files/       *.ada          the tasks: specification given, body to be written
    solutions/   *.ada          reference solutions (see below)
    yaml/        *.yaml         the same tasks in the per-task YAML form
    spark_numpy_simple.jsonl
```

`scripts/spark_verify.py` is the checker. `scripts/spark_negative_control.py`
is the test that the checker actually rejects things.

## The file format

Ada wants a package specification and a package body in two separate files.
To keep one file per task, a task is a single GNAT multi-unit source
(`.ada`) holding the specification followed by the body; the harness runs
`gnatchop` to split it before proving. The section markers are Ada comments:

```ada
--  <vc-preamble>
package Np_Abs_Spec with SPARK_Mode is
   ...types and spec functions...
--  </vc-preamble>

--  <vc-spec>
   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) with
     Pre  => ...,
     Post => ...;

end Np_Abs_Spec;

package body Np_Abs_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>
--  </vc-helpers>

--  <vc-code>
   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Abs_Vec;
--  </vc-code>

--  <vc-postamble>
end Np_Abs_Spec;
--  </vc-postamble>
```

Two differences from the Dafny and Verus layouts, both forced by Ada:

- **`vc-spec` comes before `vc-helpers`.** Helpers live in the package
  body's declarative part, which cannot precede the specification.
- **`vc-spec` carries the package frame** (`end Unit;` and
  `package body Unit ... is`). The frame is not editable, so it is safe
  there, and it keeps every byte of the file inside a section so the JSONL
  form round-trips exactly.

The unfilled body carries `pragma Assume (False)`, which plays the part
Dafny's `assume {:axiom} false` plays: the task is to replace it with
something real. As with the other tracks' `tasks/` folders, **every task
file in `files/` compiles as it stands** (checked with `gnatchop` followed
by `gcc -gnat2022 -gnatc` over all 26); nothing here belongs in an
`issues/` folder.

## What counts as a pass

`scripts/spark_verify.py` accepts a submission only if all of:

1. no verification bypass appears in the editable sections;
2. the chopped sources compile;
3. GNATprove emitted **at least one check**;
4. nothing is left unproved;
5. nothing is justified away.

Condition 3 is the one worth explaining. **GNATprove exits 0 with an empty
summary for code it never analysed** — an empty `SPARK_Mode` region, a body
excluded from analysis, a spec with no obligations. A harness that checks
only the exit status and the unproved count scores that as a pass. It is a
green light for a proof that never happened, and it is easy to produce by
accident. Requiring a non-zero check count closes it, and
`scripts/spark_negative_control.py` includes it as one of its four mutants.

Bypasses rejected in the editable sections: `pragma Assume`,
`pragma Annotate (GNATprove, False_Positive|Intentional, ...)`,
`SPARK_Mode => Off`, `pragma Suppress`, `pragma Warnings (Off)`,
`Unchecked_Conversion`, `pragma Import`.

`pragma Assert` and `pragma Loop_Invariant` are **not** bypasses — GNATprove
proves them like any other check — and are expected in most solutions.

## Running it

Requires a SPARK toolchain on `PATH` (`gnatprove` and `gnatchop`). The
easiest route is [Alire](https://alire.ada.dev): `alr toolchain --select`
then `alr install gnatprove`.

```
python scripts/spark_verify.py benchmarks/spark/numpy_simple/files/NpAbs-spec.ada
python scripts/spark_verify.py --json benchmarks/spark/numpy_simple/solutions/*.ada
python scripts/spark_negative_control.py
```

Verified on FSF GNAT 15.0 / SPARK with Why3 1.7.1, Alt-Ergo 2.6.0 and
cvc5 1.2.1, at `--level=2`.

## Reference solutions

`numpy_simple/solutions/` holds a worked solution for every task. The other
tracks do not ship these; they are included here so that anyone can confirm
the seed set is actually dischargeable rather than taking it on trust, and
so that a harness change can be regression-tested. **All 26 discharge at
`--level=2` with 0 unproved and 0 justified** — 387 checks in total (28 by
flow analysis, 359 by the provers), about 45 s wall for the whole set on a
laptop.

They are never shown to a model — the harness reads only `files/`.

## Translation discipline

Each task is a translation of the same-named Dafny task in
`benchmarks/dafny/numpy_simple`. The Dafny specification is the authority.
The rule followed was: **preserve the meaning of the specification, or skip
the task and say why.** No postcondition was weakened to make a translation
land.

Two adaptations are uniform across the set and are properties of the
language, not of any individual task:

**Bounded integers.** Dafny's `int` is a mathematical integer; Ada's
`Integer` is a machine integer, and GNATprove requires every arithmetic
operation to be proved in range. Each task therefore fixes a concrete
bounded domain — typically `Max_Index = 1_000` and
`Max_Value = 10_000`, widened per task where the operation needs headroom
(`Prod_Type` for products, `Total_Type` for running sums). Postconditions
are unchanged; the domain they are proved over is finite. This makes the
SPARK tasks *strictly harder* in one respect: an implementation must also
prove absence of overflow, which the Dafny version never has to.

**Explicit division semantics.** Dafny's `/` and `%` on `int` are Euclidean;
Ada's `/` truncates toward zero and Ada's `mod` is floor-mod. They agree
only for a positive divisor. `NpFloorDivide` and `NpMod` therefore restrict
the divisor to be positive — a restriction of the domain, stated in the
preamble — rather than silently proving a different operation. `NpFloorDivide`
names the intended operation as a spec function, `Floor_Div`.

## What is not in the seed set, and why

26 of the 58 `numpy_simple` tasks are translated. The other 32 were skipped
rather than weakened. Grouped by what blocks them:

**Dafny `real` (6).** `NpCountnonzero`, `NpHistogram`, `NpIntersect`,
`NpPoly`, `NpPolyder`, `NpSelect`. Dafny's `real` is the mathematical reals.
Ada's `Float` and `Long_Float` are IEEE binary floats. Translating one to
the other would change what the specification says while appearing not to,
which is exactly the failure mode this track should not introduce. A
faithful route exists — `SPARK.Big_Reals` — and is left open.

**Recursive specification functions (6).** `NpSum`, `NpProd`, `NpPower`,
`NpInvert`, `NpLeftShift`, `NpRightShift`. All define the specification
through a recursive function (`SumRange`, `IntPow`, `pow2`). SPARK expresses
these fine, with `Subprogram_Variant` for termination, but each also needs a
bound lemma to keep the recursive function itself overflow-free in bounded
arithmetic. That is real proof work, not a translation question. Deferred,
not blocked.

**No non-degenerate bounded domain (1).** `NpCumProd`. A running product
over up to *n* elements needs a domain in which the product stays in range;
for any interesting *n* that forces the element range down to `{-1, 0, 1}`,
at which point the task is no longer the task. `NpCumSum` has the same shape
and does have a workable domain, so it is included.

**Set, multiset and permutation postconditions (3).** `NpSort`, `NpArgsort`,
`NpUniqueall`. The postconditions quantify over multiset counts or over
element distinctness. SPARK can state these with a ghost counting function;
discharging them is a substantial development. Deferred.

**Matrices as sequences-of-sequences (8).** `NpBroadcast`, `NpColumnStack`,
`NpDiagonal`, `NpFlatten`, `NpRavel`, `NpReshape`, `NpTranspose`, `NpTril`.
Ada's constrained two-dimensional arrays are the natural target and several
of these are straightforward; they are a coherent second slice of work
rather than a scattering of odds and ends, so they were kept together for a
follow-up.

**Strings (2).** `NpCenter`, `NpIsalpha`. Dafny's `string` is an unbounded
sequence of characters with slicing. Bounded strings in Ada change the
length algebra the specification is written in.

**Number theory (2).** `NpGcd`, `NpLcm`. The maximality and divisibility
clauses quantify over every common divisor. Provable, but they need
supporting lemmas.

**Higher-order specifications (1).** `NpPiecewise` takes arrays of predicate
and transform *functions* and applies them. SPARK restricts
access-to-subprogram values sharply; there is no faithful direct target.

**Dafny datatypes with pattern matching (1).** `NpShape` specifies over a
three-way discriminated union of nested sequences of `real`. Both halves of
that — the variant type and the `real` — would have to be rephrased.

**Shape depends on the result (1).** `NpArange`. The result's length is a
computed function of the arguments. The natural Ada shape has the caller
pre-size the `out` array, which moves the length obligation out of the
postcondition and into the precondition — a different thing to prove.
Deferred pending a shape that keeps it where Dafny has it.

**Near-duplicate (1).** `NpRemainder` is `NpMod` under another name; only
one was translated.

## Extending the track

The seed set is deliberately the easy tier. Growing it means picking a group
from the list above, translating with the same discipline (meaning
preserved, or skipped and logged), and adding a reference solution that
discharges. `scripts/spark_verify.py --json` over `solutions/` is the
regression test, and `scripts/spark_negative_control.py` is the check that
the checker still bites.

If a translation cannot preserve a specification's meaning, the right answer
is to leave it out and add a line to the list above. A benchmark that
quietly weakens its own specifications measures nothing.
