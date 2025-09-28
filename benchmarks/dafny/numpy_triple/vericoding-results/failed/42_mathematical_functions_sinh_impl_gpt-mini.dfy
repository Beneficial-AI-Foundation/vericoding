// <vc-preamble>
// Uninterpreted function for mathematical exponential
ghost function Exp(x: real): real

// Helper function to define hyperbolic sine mathematically
ghost function SinhValue(x: real): real
{
  (Exp(x) - Exp(-x)) / 2.0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): non-ghost wrapper for Exp */
function Exp_impl(x: real): real {
  Exp(x)
}

/* helper modified by LLM (iteration 5): non-ghost SinhValue implementation using Exp_impl */
function SinhValue_impl(x: real): real {
  (Exp_impl(x) - Exp_impl(-x)) / 2.0
}

/* helper modified by LLM (iteration 5): lemma equating SinhValue_impl with ghost SinhValue */
lemma SinhValue_impl_eq(x: real)
  ensures SinhValue_impl(x) == SinhValue(x)
{
  assert Exp_impl(x) == Exp(x);
  assert Exp_impl(-x) == Exp(-x);
  assert SinhValue_impl(x) == (Exp_impl(x) - Exp_impl(-x)) / 2.0;
  assert SinhValue(x) == (Exp(x) - Exp(-x)) / 2.0;
  assert SinhValue_impl(x) == SinhValue(x);
}

/* helper modified by LLM (iteration 5): lemma SinhValue_odd proving oddness of SinhValue */
lemma SinhValue_odd(x: real)
  ensures SinhValue(-x) == -SinhValue(x)
{
  assert SinhValue(-x) == (Exp(-x) - Exp(-(-x))) / 2.0;
  assert -(-x) == x;
  assert (Exp(-x) - Exp(x)) / 2.0 == -(Exp(x) - Exp(-x)) / 2.0;
  assert SinhValue(-x) == -(Exp(x) - Exp(-x)) / 2.0;
  assert SinhValue(-x) == -SinhValue(x);
}

/* helper modified by LLM (iteration 5): lemma SinhValue_zero proving SinhValue(0)=0 */
lemma SinhValue_zero()
  ensures SinhValue(0.0) == 0.0
{
  assert -0.0 == 0.0;
  assert SinhValue(0.0) == (Exp(0.0) - Exp(-0.0)) / 2.0;
  assert Exp(-0.0) == Exp(0.0);
  assert SinhValue(0.0) == 0.0;
}

// </vc-helpers>

// <vc-spec>
method Sinh(x: seq<real>) returns (result: seq<real>)
  // No preconditions - hyperbolic sine is defined for all real numbers
  ensures |result| == |x|
  
  // Core mathematical definition: sinh(x) = (e^x - e^(-x))/2
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == SinhValue(x[i])
  
  // Odd function property: sinh(-x) = -sinh(x)
  ensures forall i :: 0 <= i < |x| ==>
    SinhValue(-x[i]) == -result[i]
  
  // Zero property: sinh(0) = 0
  ensures forall i :: 0 <= i < |x| ==>
    x[i] == 0.0 ==> result[i] == 0.0
  
  // Sign property: sinh(x) has the same sign as x
  ensures forall i :: 0 <= i < |x| ==>
    (x[i] > 0.0 ==> result[i] > 0.0) &&
    (x[i] < 0.0 ==> result[i] < 0.0)
  
  // Monotonicity property: sinh is strictly increasing
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| ==>
    x[i] < x[j] ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build result sequence using non-ghost SinhValue_impl and prove spec using ghost lemma */
  var n := |x|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == SinhValue_impl(x[j])
  {
    result := result + [SinhValue_impl(x[i])];
    i := i + 1;
  }

  ghost var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> result[j] == SinhValue(x[j])
  {
    SinhValue_impl_eq(x[k]);
    assert result[k] == SinhValue_impl(x[k]);
    assert SinhValue_impl(x[k]) == SinhValue(x[k]);
    k := k + 1;
  }
}

// </vc-code>
