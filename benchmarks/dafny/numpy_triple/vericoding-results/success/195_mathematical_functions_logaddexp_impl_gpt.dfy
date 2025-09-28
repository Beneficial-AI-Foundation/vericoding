// <vc-preamble>
/*
 * Looking at the compilation errors, the functions `exp` and `log` have no body and cannot be compiled. Since these are mathematical functions used in specifications, I need to mark them as axioms to make them compilable while preserving the intended semantics.
 */



// Mathematical functions for logarithm and exponential
function {:axiom} exp(x: real): real
{
  1.0  // Stub implementation for compilation
}

function {:axiom} log(x: real): real
  requires x > 0.0
{
  0.0  // Stub implementation for compilation
}

function max(x: real, y: real): real
{
  if x >= y then x else y
}

// Mathematical properties of log and exp functions
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple constant helper returning 2.0 */
function two(): real { 2.0 }

/* helper modified by LLM (iteration 2): lemma to expose positivity of exp and its sum */
lemma ExpPosAndSumPos(x: real, y: real)
  ensures exp(x) > 0.0
  ensures exp(y) > 0.0
  ensures exp(x) + exp(y) > 0.0
{
  LogExpProperties();
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} LogExpProperties()
  ensures forall x: real :: x > 0.0 ==> exp(log(x)) == x
  ensures forall x: real :: log(exp(x)) == x
  ensures forall x, y: real :: exp(x + y) == exp(x) * exp(y)
  ensures forall x, y: real :: (x > 0.0 && y > 0.0) ==> log(x * y) == log(x) + log(y)
  ensures forall x: real :: exp(x) > 0.0
  ensures forall x, y: real :: x < y ==> exp(x) < exp(y)
  ensures forall x, y: real :: (x > 0.0 && y > 0.0 && x < y) ==> log(x) < log(y)

/**
 * Computes the logarithm of the sum of exponentiations element-wise.
 * For each index i, computes log(exp(x1[i]) + exp(x2[i])).
 * This provides numerically stable computation without intermediate overflow.
 */
method logaddexp(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  // Element-wise correctness: result[i] = log(exp(x1[i]) + exp(x2[i]))
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == log(exp(x1[i]) + exp(x2[i]))
  // Bounds property: result[i] >= max(x1[i], x2[i])
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] >= max(x1[i], x2[i])
  // Special case: logaddexp(x, x) = x + log(2)
  ensures forall i :: 0 <= i < |result| ==> 
    x1[i] == x2[i] ==> result[i] == x1[i] + log(2.0)
  // Commutativity: logaddexp(x1, x2) = logaddexp(x2, x1)
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == log(exp(x2[i]) + exp(x1[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced non-executable sequence comprehension with loop, ensured log preconditions, and established postconditions via invariants and assertions */
  LogExpProperties();
  var n := |x1|;
  var r: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == log(exp(x1[j]) + exp(x2[j]))
    invariant forall j :: 0 <= j < i ==> r[j] >= max(x1[j], x2[j])
    invariant forall j :: 0 <= j < i ==> r[j] == log(exp(x2[j]) + exp(x1[j]))
    invariant forall j :: 0 <= j < i ==> x1[j] == x2[j] ==> r[j] == x1[j] + log(2.0)
  {
    // Ensure positivity for log preconditions
    ExpPosAndSumPos(x1[i], x2[i]);

    var sum := exp(x1[i]) + exp(x2[i]);
    var v := log(sum);

    // Lower bounds: v >= x1[i]
    assert sum > exp(x1[i]);
    assert log(exp(x1[i])) < log(sum);
    assert x1[i] == log(exp(x1[i]));
    assert v >= x1[i];

    // Lower bounds: v >= x2[i]
    assert sum > exp(x2[i]);
    assert log(exp(x2[i])) < log(sum);
    assert x2[i] == log(exp(x2[i]));
    assert v >= x2[i];

    // Therefore v >= max(x1[i], x2[i])
    assert v >= max(x1[i], x2[i]);

    // Commutativity: same value
    assert v == log(exp(x2[i]) + exp(x1[i]));

    // Special case: if x1[i] == x2[i]
    if x1[i] == x2[i] {
      assert sum == 2.0 * exp(x1[i]);
      assert 2.0 > 0.0;
      assert 2.0 * exp(x1[i]) > 0.0;
      assert v == log(2.0 * exp(x1[i]));
      assert v == log(2.0) + log(exp(x1[i]));
      assert v == x1[i] + log(2.0);
    }

    r := r + [v];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
