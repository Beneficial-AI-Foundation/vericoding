// <vc-preamble>
// Ghost function to represent square root for specification purposes
ghost function {:axiom} Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x

// Ghost function to represent absolute value
ghost function {:axiom} Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures Abs(x) == x || Abs(x) == -x
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x

/**
 * Computes the Chebyshev weight function 1/sqrt(1 - x²) for each element in the input sequence.
 * 
 * The weight function is well-defined for all x in the open interval (-1, 1).
 * For numerical stability, the implementation should use the factored form
 * 1/(sqrt(1+x) * sqrt(1-x)).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove positivity of denominators inside (-1,1) and relate 1 - x^2 */
lemma PosDenoms(x: real)
  requires -1.0 < x && x < 1.0
  ensures 1.0 + x > 0.0
  ensures 1.0 - x > 0.0
  ensures 1.0 - x*x > 0.0
{
  assert 1.0 + x > 0.0;
  assert 1.0 - x > 0.0;
  assert (1.0 + x) * (1.0 - x) > 0.0;
  assert (1.0 + x) * (1.0 - x) == 1.0 - x*x;
}

/* helper modified by LLM (iteration 5): uniqueness of nonnegative square root */
lemma NonNegSquareRootUnique(y: real, z: real)
  requires y >= 0.0
  requires z >= 0.0
  requires z * z == y
  ensures z == Sqrt(y)
{
  var t := Sqrt(y);
  assert t >= 0.0;
  assert t * t == y;
  assert (z - t) * (z + t) == z*z - t*t;
  assert z*z - t*t == 0.0;
  assert (z - t) * (z + t) == 0.0;
  if z + t == 0.0 {
    assert z == -t;
    assert z >= 0.0 && t >= 0.0;
    assert t == 0.0;
    assert z == 0.0;
  } else {
    assert ((z - t) * (z + t)) / (z + t) == 0.0 / (z + t);
    assert z - t == 0.0;
  }
  assert z == t;
}

/* helper modified by LLM (iteration 5): show sqrt(1 - x^2) factors into sqrt(1+x)*sqrt(1-x) */
lemma SqrtProductIdentity(x: real)
  requires -1.0 < x && x < 1.0
  ensures Sqrt(1.0 - x*x) == Sqrt(1.0 + x) * Sqrt(1.0 - x)
{
  PosDenoms(x);
  var s1 := Sqrt(1.0 + x);
  var s2 := Sqrt(1.0 - x);
  assert s1 >= 0.0 && s2 >= 0.0;
  var z := s1 * s2;
  assert z >= 0.0;
  assert z * z == (s1 * s2) * (s1 * s2);
  assert (s1 * s2) * (s1 * s2) == (s1*s1) * (s2*s2);
  assert s1*s1 == 1.0 + x;
  assert s2*s2 == 1.0 - x;
  assert z*z == (1.0 + x) * (1.0 - x);
  assert (1.0 + x) * (1.0 - x) == 1.0 - x*x;
  NonNegSquareRootUnique(1.0 - x*x, z);
}

/* helper modified by LLM (iteration 5): absolute value squared equals square */
lemma AbsSquare(y: real)
  ensures Abs(y) * Abs(y) == y * y
{
  if y >= 0.0 {
    assert Abs(y) == y;
  } else {
    assert y < 0.0;
    assert Abs(y) == -y;
  }
  assert Abs(y) * Abs(y) == y * y;
}

/* helper modified by LLM (iteration 5): sqrt is strictly positive when its argument is strictly positive */
lemma SqrtPositive(y: real)
  requires y > 0.0
  ensures Sqrt(y) > 0.0
{
  var s := Sqrt(y);
  assert s >= 0.0;
  if s == 0.0 {
    assert s * s == 0.0;
    assert s * s == y;
    assert y == 0.0;
    assert false;
  }
}

// </vc-helpers>

// <vc-spec>
method ChebWeight(x: seq<real>) returns (w: seq<real>)
  // Input validation: all elements must be in the open interval (-1, 1)
  requires |x| > 0
  requires forall i :: 0 <= i < |x| ==> -1.0 < x[i] < 1.0
  
  // Output has same length as input
  ensures |w| == |x|
  
  // Primary mathematical formula: w[i] = 1/sqrt(1 - x[i]²)
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i])
  
  // Result is always positive for valid inputs
  ensures forall i :: 0 <= i < |x| ==> w[i] > 0.0
  
  // Symmetry property: w(-x) = w(x)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> 
    w[i] == w[j]
  
  // Numerical stability: equivalent factored form
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] == 1.0 / (Sqrt(1.0 + x[i]) * Sqrt(1.0 - x[i]))
  
  // Mathematical bounds: weight function approaches infinity as x approaches ±1
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] >= 1.0 / Sqrt(1.0 - Abs(x[i]) * Abs(x[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fix sequence comprehension syntax and provide structured proofs for postconditions */
  var n := |x|;
  w := seq i | 0 <= i < n :: 1.0 / Sqrt(1.0 - x[i] * x[i]);

  assert |w| == |x|;

  // Primary formula by construction
  assert forall i: int :: 0 <= i < n ==> w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i]);

  // Positivity of weights
  assert forall i: int :: 0 <= i < n ==> w[i] > 0.0
  by {
    assert -1.0 < x[i] && x[i] < 1.0;
    PosDenoms(x[i]);
    assert 1.0 - x[i] * x[i] > 0.0;
    SqrtPositive(1.0 - x[i] * x[i]);
    assert Sqrt(1.0 - x[i] * x[i]) > 0.0;
    assert w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i]);
  };

  // Symmetry: w(-x) = w(x)
  assert forall i: int, j: int :: 0 <= i < n && 0 <= j < n && x[i] == -x[j] ==> w[i] == w[j]
  by {
    assert x[i] * x[i] == (-x[j]) * (-x[j]);
    assert (-x[j]) * (-x[j]) == x[j] * x[j];
    assert w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i]);
    assert w[j] == 1.0 / Sqrt(1.0 - x[j] * x[j]);
  };

  // Factored form equivalence
  assert forall i: int :: 0 <= i < n ==> w[i] == 1.0 / (Sqrt(1.0 + x[i]) * Sqrt(1.0 - x[i]))
  by {
    assert -1.0 < x[i] && x[i] < 1.0;
    PosDenoms(x[i]);
    SqrtProductIdentity(x[i]);
    assert w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i]);
    assert Sqrt(1.0 - x[i] * x[i]) == Sqrt(1.0 + x[i]) * Sqrt(1.0 - x[i]);
  };

  // Bounds using Abs
  assert forall i: int :: 0 <= i < n ==> w[i] >= 1.0 / Sqrt(1.0 - Abs(x[i]) * Abs(x[i]))
  by {
    AbsSquare(x[i]);
    assert 1.0 - Abs(x[i]) * Abs(x[i]) == 1.0 - x[i] * x[i];
    assert 1.0 / Sqrt(1.0 - Abs(x[i]) * Abs(x[i])) == 1.0 / Sqrt(1.0 - x[i] * x[i]);
    assert w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i]);
    assert w[i] >= w[i];
  };
}

// </vc-code>
