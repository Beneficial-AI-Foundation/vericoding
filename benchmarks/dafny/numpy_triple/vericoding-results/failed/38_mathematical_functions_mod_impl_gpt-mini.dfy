// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide FloorInt and its bounds lemma */
function FloorInt(x: real): int { x.Floor }
lemma FloorInt_bounds(x: real)
  ensures (FloorInt(x) as real) <= x && x < (FloorInt(x) as real) + 1
{
  assert FloorInt(x) == x.Floor;
  assert (x.Floor as real) <= x;
  assert x < (x.Floor as real) + 1;
}
// </vc-helpers>

// <vc-spec>
method numpy_mod(n: nat, x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Precondition: vectors must have fixed length n and all divisors must be non-zero
  requires |x1| == n && |x2| == n
  requires forall i :: 0 <= i < |x2| ==> x2[i] != 0.0
  
  // Postcondition: result has same fixed length as inputs
  ensures |result| == n
  
  // Postcondition: each element satisfies the mathematical remainder properties
  // (approximating floating-point floor behavior with real floor)
  ensures forall i :: 0 <= i < |result| ==>
    var r := result[i];
    var a := x1[i];
    var b := x2[i];
    // Basic remainder property: a = floor(a/b) * b + r
    a == (a / b).Floor as real * b + r &&
    // Result has same sign as divisor and proper bounds
    (b > 0.0 ==> r >= 0.0 && r < b) &&
    (b < 0.0 ==> r <= 0.0 && r > b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement element-wise modulo using FloorInt and its lemma */
  var arr := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall k :: 0 <= k < i ==>
      x1[k] == (FloorInt(x1[k] / x2[k]) as real) * x2[k] + arr[k] &&
      (x2[k] > 0.0 ==> arr[k] >= 0.0 && arr[k] < x2[k]) &&
      (x2[k] < 0.0 ==> arr[k] <= 0.0 && arr[k] > x2[k])
    decreases n - i
  {
    var a := x1[i];
    var b := x2[i];
    var q := FloorInt(a / b);
    FloorInt_bounds(a / b);
    var r := a - (q as real) * b;
    arr[i] := r;
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
