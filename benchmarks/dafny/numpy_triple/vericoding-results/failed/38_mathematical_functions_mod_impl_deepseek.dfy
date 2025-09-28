// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed FloorProperty lemma with proper assertions and real arithmetic */
lemma FloorProperty(a: real, b: real) returns (r: real)
  requires b != 0.0
  ensures a == (a / b).Floor as real * b + r
  ensures (b > 0.0 ==> r >= 0.0 && r < b)
  ensures (b < 0.0 ==> r <= 0.0 && r > b)
{
  r := a - (a / b).Floor as real * b;
  if b > 0.0 {
    assert (a / b).Floor as real <= a / b < (a / b).Floor as real + 1.0;
    assert (a / b).Floor as real * b <= a < ((a / b).Floor as real + 1.0) * b;
    assert 0.0 <= r < b;
  } else {
    assert (a / b).Floor as real <= a / b < (a / b).Floor as real + 1.0;
    assert ((a / b).Floor as real + 1.0) * b < a <= (a / b).Floor as real * b;
    assert r <= 0.0 && r > b;
  }
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
/* code modified by LLM (iteration 5): Fixed loop invariant with explicit calls to FloorProperty lemma */
{
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      var r_val := result[j];
      var a_val := x1[j];
      var b_val := x2[j];
      a_val == (a_val / b_val).Floor as real * b_val + r_val &&
      (b_val > 0.0 ==> r_val >= 0.0 && r_val < b_val) &&
      (b_val < 0.0 ==> r_val <= 0.0 && r_val > b_val)
  {
    var remainder: real;
    remainder := FloorProperty(x1[i], x2[i]);
    result := result + [remainder];
    i := i + 1;
  }
}
// </vc-code>
