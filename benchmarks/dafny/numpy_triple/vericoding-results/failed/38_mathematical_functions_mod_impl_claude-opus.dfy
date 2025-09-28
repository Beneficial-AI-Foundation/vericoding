// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiplication inequalities in FloorModProperties */
lemma FloorModProperties(a: real, b: real)
  requires b != 0.0
  ensures var r := a - (a / b).Floor as real * b;
    (b > 0.0 ==> r >= 0.0 && r < b) &&
    (b < 0.0 ==> r <= 0.0 && r > b)
{
  var q := (a / b).Floor as real;
  var r := a - q * b;
  
  // Floor property: q <= a/b < q + 1
  assert q <= a / b < q + 1.0;
  
  if b > 0.0 {
    // When b > 0, multiplication preserves inequality direction
    // q <= a/b implies q*b <= a
    // a/b < q+1 implies a < (q+1)*b
    assert q * b <= (a / b) * b == a;
    assert (a / b) * b == a < (q + 1.0) * b;
    assert 0.0 <= r < b;
  } else {
    // When b < 0, multiplication reverses inequality direction  
    // q <= a/b implies q*b >= a (since b < 0)
    // a/b < q+1 implies a > (q+1)*b (since b < 0)
    assert q * b >= (a / b) * b == a;
    assert (a / b) * b == a > (q + 1.0) * b;
    assert b < r <= 0.0;
  }
}

function mod_real(a: real, b: real): real
  requires b != 0.0
  ensures b > 0.0 ==> mod_real(a, b) >= 0.0 && mod_real(a, b) < b
  ensures b < 0.0 ==> mod_real(a, b) <= 0.0 && mod_real(a, b) > b
  ensures a == (a / b).Floor as real * b + mod_real(a, b)
{
  FloorModProperties(a, b);
  a - (a / b).Floor as real * b
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
/* code modified by LLM (iteration 5): No changes needed - implementation is correct */
{
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      var r := result[j];
      var a := x1[j];
      var b := x2[j];
      a == (a / b).Floor as real * b + r &&
      (b > 0.0 ==> r >= 0.0 && r < b) &&
      (b < 0.0 ==> r <= 0.0 && r > b)
  {
    var r := mod_real(x1[i], x2[i]);
    result := result + [r];
    i := i + 1;
  }
}
// </vc-code>
