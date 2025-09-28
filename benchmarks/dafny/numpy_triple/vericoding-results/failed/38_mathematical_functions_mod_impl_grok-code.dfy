// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed type mismatches by explicitly casting quot to real and removing the var declaration in ensures */
function compute_remainder(a: real, b: real): (result: real)
  requires b != 0.0
  ensures a == ((a / b).Floor as real) * b + result
  ensures b > 0.0 ==> result >= 0.0 && result < b
  ensures b < 0.0 ==> result <= 0.0 && result > b
{
  var quot := (a / b).Floor;
  a - (quot as real * b)
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
/* code modified by LLM (iteration 4): No changes needed, as the code is correct */
{
  result := [];
  for i : nat := 0 to n {
    result := result + [compute_remainder(x1[i], x2[i])];
  }
}
// </vc-code>
