// <vc-preamble>
// Helper function to compute integer powers
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

// Bitwise left shift operation on sequences of integers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Power(2,s) >= 2 for s>0 */
lemma Power_ge_two_for_pos(s: nat)
  requires s > 0
  ensures Power(2, s) >= 2
  decreases s
{
  if s == 1 {
    assert Power(2, 1) == 2;
  } else {
    assert Power(2, s) == 2 * Power(2, s - 1);
    Power_ge_two_for_pos(s - 1);
    assert Power(2, s - 1) >= 2;
    assert 2 * Power(2, s - 1) >= 2;
  }
}

/* helper modified by LLM (iteration 4): Power equals 1 iff exponent zero */
lemma Power_one_iff_zero(s: nat)
  ensures (Power(2, s) == 1) <==> s == 0
  decreases s
{
  if s == 0 {
    assert Power(2, 0) == 1;
  } else {
    Power_ge_two_for_pos(s);
    assert Power(2, s) >= 2;
  }
}

/* helper modified by LLM (iteration 4): multiplication increases positive a when k>=2 */
lemma Mul_gt_for_k_ge_two(a: int, k: int)
  requires a > 0 && k >= 2
  ensures a * k > a
{
  var d := k - 2;
  assert d >= 0;
  assert a * d >= 0; // a>0 and d>=0 => product >=0
  assert a * k == a * 2 + a * d;
  assert a * 2 > a; // since a>0
  assert a * k > a;
}

/* helper modified by LLM (iteration 4): multiplication decreases negative a when k>=2 */
lemma Mul_lt_for_k_ge_two_neg(a: int, k: int)
  requires a < 0 && k >= 2
  ensures a * k < a
{
  var d := k - 2;
  assert d >= 0;
  assert a * d <= 0; // a<0 and d>=0 => product <=0
  assert a * k == a * 2 + a * d;
  assert a * 2 < a; // since a<0
  assert a * k < a;
}
// </vc-helpers>

// <vc-spec>
method LeftShift(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
  // Input sequences must have the same length
  requires |x1| == |x2|
  // All shift amounts must be non-negative
  requires forall i :: 0 <= i < |x2| ==> x2[i] >= 0
  
  // Output has same length as inputs
  ensures |result| == |x1|
  // Core behavior: each element is multiplied by 2^shift_amount
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] * Power(2, x2[i])
  // Identity property: shifting by 0 returns original value
  ensures forall i :: 0 <= i < |result| && x2[i] == 0 ==> result[i] == x1[i]
  // Zero preservation: shifting zero always yields zero
  ensures forall i :: 0 <= i < |result| && x1[i] == 0 ==> result[i] == 0
  // Monotonicity for positive values: left shifting increases magnitude
  ensures forall i :: 0 <= i < |result| && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i]
  // Monotonicity for negative values: left shifting decreases value (more negative)
  ensures forall i :: 0 <= i < |result| && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute shifted sequence and discharge monotonicity via lemmas */
  var n := |x1|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == x1[j] * Power(2, x2[j] as nat)
    invariant forall j :: 0 <= j < i && x1[j] > 0 && x2[j] > 0 ==> a[j] > x1[j]
    invariant forall j :: 0 <= j < i && x1[j] < 0 && x2[j] > 0 ==> a[j] < x1[j]
  {
    var k := Power(2, x2[i] as nat);
    a[i] := x1[i] * k;
    if x2[i] > 0 {
      Power_ge_two_for_pos(x2[i] as nat);
      if x1[i] > 0 {
        Mul_gt_for_k_ge_two(x1[i], k);
        assert a[i] > x1[i];
      } else if x1[i] < 0 {
        Mul_lt_for_k_ge_two_neg(x1[i], k);
        assert a[i] < x1[i];
      }
    }
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
