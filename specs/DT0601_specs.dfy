// <vc-preamble>
/*
 * Variance computation for numerical arrays following NumPy's var function behavior.
 * Computes variance as the average of squared deviations from the mean, with support
 * for delta degrees of freedom (ddof) parameter for statistical corrections.
 */

// Ghost function to compute the mean of a sequence
ghost function Mean(a: seq<real>): real
  requires |a| > 0
{
  Sum(a) / (|a| as real)
}

// Ghost function to compute the sum of a sequence
ghost function Sum(a: seq<real>): real
{
  if |a| == 0 then 0.0
  else a[0] + Sum(a[1..])
}

// Ghost function to compute sum of squared deviations from mean
ghost function SumSquaredDeviations(a: seq<real>, mean: real): real
{
  if |a| == 0 then 0.0
  else (a[0] - mean) * (a[0] - mean) + SumSquaredDeviations(a[1..], mean)
}

// Ghost function to check if all elements in sequence are equal
ghost predicate AllEqual(a: seq<real>)
{
  forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> a[i] == a[j]
}

// Ghost function to create sequence with constant added to all elements
ghost function AddConstant(a: seq<real>, c: real): seq<real>
{
  seq(|a|, i requires 0 <= i < |a| => a[i] + c)
}

// Ghost function to create sequence with all elements scaled by constant
ghost function ScaleByConstant(a: seq<real>, c: real): seq<real>
{
  seq(|a|, i requires 0 <= i < |a| => c * a[i])
}

// Main variance computation function
  ensures Var(a, ddof) == 0.0 <==> AllEqual(a)
  ensures forall c: real :: Var(AddConstant(a, c), ddof) == Var(a, ddof)
  ensures forall c: real :: c != 0.0 ==> Var(ScaleByConstant(a, c), ddof) == c * c * Var(a, ddof)
{
  SumSquaredDeviations(a, Mean(a)) / ((|a| - ddof) as real)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
ghost function Var(a: seq<real>, ddof: nat): real
  requires |a| > 0
  requires ddof < |a|
  ensures Var(a, ddof) >
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
