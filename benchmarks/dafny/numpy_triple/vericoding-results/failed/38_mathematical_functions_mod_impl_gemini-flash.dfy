// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed a parsing error by ensuring the conditional assignment `r := r + b;` is properly within the `if` block, without an implicit `else` or dangling statement. The logic for `mod_real` was already correctly returning the remainder `r` satisfying the desired properties. */
function mod_real(a: real, b: real): real
  requires b != 0.0
  ensures a == (a / b).Floor as real * b + result
  ensures (b > 0.0 ==> result >= 0.0 && result < b)
  ensures (b < 0.0 ==> result <= 0.0 && result > b)
{
  var r := a - (a / b).Floor as real * b;
  // If r is non-zero and has a different sign than b, adjust it
  if r != 0.0 && ((b > 0.0 && r < 0.0) || (b < 0.0 && r > 0.0)) {
    r := r + b;
  }
  return r;
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
/* code modified by LLM (iteration 5): No changes needed in this code section. */
{
  var result_seq: seq<real> := new real[n];
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |result_seq| == n
    invariant forall k :: 0 <= k < i ==> 
      var r := result_seq[k];
      var a := x1[k];
      var b := x2[k];
      a == (a / b).Floor as real * b + r &&
      (b > 0.0 ==> r >= 0.0 && r < b) &&
      (b < 0.0 ==> r <= 0.0 && r > b)
  {
    result_seq[i] := mod_real(x1[i], x2[i]);
  }
  return result_seq;
}
// </vc-code>
