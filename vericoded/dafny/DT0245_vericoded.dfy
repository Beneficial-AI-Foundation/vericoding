// <vc-preamble>
// Helper function to compute the sum of element-wise products of two sequences
function SumProduct(a: seq<real>, b: seq<real>): real
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0.0
  else a[0] * b[0] + SumProduct(a[1..], b[1..])
}

// Main tensor dot product method for 1-D vectors with axes=1
// </vc-preamble>

// <vc-helpers>
lemma SumProduct_unfold_at(a: seq<real>, b: seq<real>, i: nat)
  requires |a| == |b|
  requires i < |a|
  ensures SumProduct(a[i..], b[i..]) == a[i]*b[i] + SumProduct(a[i+1..], b[i+1..])
  decreases |a| - i
{
  // By definition of SumProduct on the sliced sequences
  assert SumProduct(a[i..], b[i..]) == (a[i..])[0] * (b[i..])[0] + SumProduct((a[i..])[1..], (b[i..])[1..]);
  assert (a[i..])[0] == a[i];
  assert (b[i..])[0] == b[i];
  assert (a[i..])[1..] == a[i+1..];
  assert (b[i..])[1..] == b[i+1..];
  assert SumProduct(a[i..], b[i..]) == a[i]*b[i] + SumProduct(a[i+1..], b[i+1..]);
}

// </vc-helpers>

// <vc-spec>
method tensordot(a: seq<real>, b: seq<real>, axes: nat) returns (result: real)
  // Precondition: axes must be 1 for 1-D vector case
  requires axes == 1
  // Precondition: vectors must have same length
  requires |a| == |b|
  // Postcondition: result equals sum of element-wise products
  ensures result == SumProduct(a, b)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var acc: real := 0.0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant acc + SumProduct(a[i..], b[i..]) == SumProduct(a, b)
  {
    var prod := a[i] * b[i];
    SumProduct_unfold_at(a, b, i);
    acc := acc + prod;
    i := i + 1;
  }
  result := acc;
}

// </vc-code>
