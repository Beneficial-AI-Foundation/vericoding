// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors by converting int to real where needed */
lemma ModuloProperty(a: real, b: real)
  requires b != 0.0
  ensures 
    var r := a - ((a / b).Floor as real) * b;
    a == ((a / b).Floor as real) * b + r &&
    (b > 0.0 ==> r >= 0.0 && r < b) &&
    (b < 0.0 ==> r <= 0.0 && r > b)
{
  var r := a - ((a / b).Floor as real) * b;
  // The first part is by definition
  assert a == ((a / b).Floor as real) * b + r;

  if b > 0.0 {
    // Property of floor: (a / b).Floor <= a / b
    assert ((a / b).Floor as real) <= a / b;
    // Multiply both sides by b (positive, so inequality preserved)
    assert ((a / b).Floor as real) * b <= a;
    // Therefore r = a - ... >= 0
    assert r >= 0.0;

    // Property of floor: a / b < (a / b).Floor + 1.0
    assert a / b < ((a / b).Floor as real) + 1.0;
    // Multiply both sides by b (positive)
    assert a < (((a / b).Floor as real) + 1.0) * b;
    // Expand: a < ((a / b).Floor as real) * b + b
    // Therefore r = a - ((a / b).Floor as real) * b < b
    assert r < b;
  } else {
    // b < 0.0
    // Property of floor: (a / b).Floor <= a / b
    assert ((a / b).Floor as real) <= a / b;
    // Multiply both sides by b (negative, so inequality reverses)
    assert ((a / b).Floor as real) * b >= a;
    // Therefore r = a - ... <= 0
    assert r <= 0.0;

    // Property of floor: a / b < (a / b).Floor + 1.0
    assert a / b < ((a / b).Floor as real) + 1.0;
    // Multiply both sides by b (negative, so inequality reverses)
    assert a > (((a / b).Floor as real) + 1.0) * b;
    // Expand: a > ((a / b).Floor as real) * b + b
    // Therefore r = a - ((a / b).Floor as real) * b > b
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
  /* code modified by LLM (iteration 5): Fixed type conversion errors in modulo computation */
  var resultSeq := [];
  if n > 0 {
    for i := 0 to n-1
      invariant |resultSeq| == i
      invariant forall j :: 0 <= j < i ==> 
        resultSeq[j] == x1[j] - ((x1[j]/x2[j]).Floor as real) * x2[j] &&
        x1[j] == ((x1[j]/x2[j]).Floor as real) * x2[j] + resultSeq[j] &&
        (x2[j] > 0.0 ==> resultSeq[j] >= 0.0 && resultSeq[j] < x2[j]) &&
        (x2[j] < 0.0 ==> resultSeq[j] <= 0.0 && resultSeq[j] > x2[j])
    {
      var elem := x1[i] - ((x1[i]/x2[i]).Floor as real) * x2[i];
      ModuloProperty(x1[i], x2[i]); // This proves the properties for elem
      resultSeq := resultSeq + [elem];
    }
  }
  result := resultSeq;
}
// </vc-code>
