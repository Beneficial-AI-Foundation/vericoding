// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened modulo properties lemma with explicit bounds proofs */
lemma FloorProperties(x: real)
  ensures x - 1.0 < x.Floor as real <= x
{
  // Floor properties are built into Dafny
}

lemma ModuloProperties(a: real, b: real)
  requires b != 0.0
  ensures var r := a - (a / b).Floor as real * b;
    a == (a / b).Floor as real * b + r &&
    (b > 0.0 ==> r >= 0.0 && r < b) &&
    (b < 0.0 ==> r <= 0.0 && r > b)
{
  var q := (a / b).Floor as real;
  var r := a - q * b;
  
  // First property follows directly from definition
  assert a == q * b + r;
  
  // For the bounds, we use the floor property
  FloorProperties(a / b);
  assert a / b - 1.0 < q <= a / b;
  
  if b > 0.0 {
    // From q <= a/b, multiply by positive b: q*b <= a, so r = a - q*b >= 0
    calc {
      q;
      <= a / b;
      == { assert b > 0.0; }
      a / b;
    }
    assert q * b <= a;
    assert r >= 0.0;
    
    // From a/b - 1 < q, multiply by positive b: (a/b - 1)*b < q*b, so a - b < q*b, so r < b
    calc {
      a / b - 1.0;
      < q;
      == { assert b > 0.0; }
      q;
    }
    assert (a / b - 1.0) * b < q * b;
    assert a - b < q * b;
    assert r < b;
  }
  
  if b < 0.0 {
    // From q <= a/b, multiply by negative b: q*b >= a, so r = a - q*b <= 0
    calc {
      q;
      <= a / b;
      == { assert b < 0.0; }
      a / b;
    }
    assert q * b >= a;
    assert r <= 0.0;
    
    // From a/b - 1 < q, multiply by negative b: (a/b - 1)*b > q*b, so a - b > q*b, so r > b
    calc {
      a / b - 1.0;
      < q;
      == { assert b < 0.0; }
      q;
    }
    assert (a / b - 1.0) * b > q * b;
    assert a - b > q * b;
    assert r > b;
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
{
  /* code modified by LLM (iteration 5): call ModuloProperties before computing remainder to establish properties */
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      (var r := result[j];
       var a := x1[j];
       var b := x2[j];
       a == (a / b).Floor as real * b + r &&
       (b > 0.0 ==> r >= 0.0 && r < b) &&
       (b < 0.0 ==> r <= 0.0 && r > b))
  {
    var a := x1[i];
    var b := x2[i];
    ModuloProperties(a, b);
    var quotient := (a / b).Floor as real;
    var remainder := a - quotient * b;
    result := result + [remainder];
    i := i + 1;
  }
}
// </vc-code>
