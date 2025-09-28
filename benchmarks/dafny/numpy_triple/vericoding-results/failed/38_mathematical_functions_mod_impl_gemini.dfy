// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): [inlined helper logic and added proof] */
  result := seq(n, i => x1[i] - (x1[i] / x2[i]).Floor as real * x2[i]);

  forall i | 0 <= i < n
    ensures
      var r := result[i];
      var a := x1[i];
      var b := x2[i];
      a == (a / b).Floor as real * b + r &&
      (b > 0.0 ==> r >= 0.0 && r < b) &&
      (b < 0.0 ==> r <= 0.0 && r > b)
  {
    var a := x1[i];
    var b := x2[i];
    var q := (a / b).Floor as real;
    var div := a / b;

    if b > 0.0 {
      assert q <= div;
      assert q * b <= div * b == a;
      
      assert div < q + 1.0;
      assert a == div * b < (q + 1.0) * b == q * b + b;
    } else { // b < 0.0
      assert q <= div;
      assert q * b >= div * b == a;

      assert div < q + 1.0;
      assert a == div * b > (q + 1.0) * b == q * b + b;
    }
  }
}
// </vc-code>
