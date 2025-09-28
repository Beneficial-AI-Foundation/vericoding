// <vc-preamble>
// Helper function to compute maximum of two integers
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

/**
 * Subtract one Hermite series from another.
 * Returns the difference of two Hermite series c1 - c2.
 * The sequences of coefficients are from lowest order term to highest.
 * Shorter arrays are implicitly padded with zeros for subtraction.
 */
// </vc-preamble>

// <vc-helpers>
lemma Max_ge(a: int, b: int)
  ensures Max(a,b) >= a && Max(a,b) >= b
{
  if a >= b {
    assert Max(a,b) == a;
    assert a >= a && a >= b;
  } else {
    assert Max(a,b) == b;
    assert b >= a && b >= b;
  }
}
// </vc-helpers>

// <vc-spec>
method hermesub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result length equals the maximum of input lengths
    ensures |result| == Max(|c1|, |c2|)
    // Each coefficient is the component-wise difference, with implicit zero padding
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  var n := Max(|c1|, |c2|);
  Max_ge(|c1|, |c2|);
  assert n >= |c1| && n >= |c2|;
  assert |c1| >= 0;
  assert n >= 0;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (if j < |c1| then c1[j] else 0.0) - (if j < |c2| then c2[j] else 0.0)
  {
    var v := (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0);
    a[i] := v;
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
