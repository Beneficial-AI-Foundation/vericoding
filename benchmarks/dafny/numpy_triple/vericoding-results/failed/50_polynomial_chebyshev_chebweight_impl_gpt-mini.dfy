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
/* helper modified by LLM (iteration 5): ensure uniqueness of nonnegative square root */
lemma SquareRootUnique(x: real, y: real)
  requires x >= 0.0
  requires y >= 0.0
  requires y * y == x
  ensures y == Sqrt(x)
{
  var s := Sqrt(x);
  // (y - s)*(y + s) == y*y - s*s == x - x == 0
  assert (y - s) * (y + s) == 0.0;
  if y + s == 0.0 {
    // then both nonnegative summands must be zero
    assert y == 0.0;
    assert s == 0.0;
  } else {
    // y + s != 0.0, divide both sides of the product equality by y + s
    // ((y - s)*(y + s)) / (y + s) == 0.0
    var tmp := ((y - s) * (y + s)) / (y + s);
    assert tmp == 0.0;
    // cancellation: ((y - s)*(y + s)) / (y + s) == y - s
    // Prove cancellation by simple algebraic steps
    assert (((y - s) * (y + s)) / (y + s)) * (y + s) == (y - s) * (y + s);
    // From previous two facts, we get y - s == 0.0
    assert y - s == 0.0;
  }
  assert y == s;
}

/* helper modified by LLM (iteration 5): sqrt multiplicative property */
lemma SqrtMul(a: real, b: real)
  requires a >= 0.0
  requires b >= 0.0
  ensures Sqrt(a * b) == Sqrt(a) * Sqrt(b)
{
  var p := Sqrt(a) * Sqrt(b);
  assert p >= 0.0;
  assert p * p == a * b;
  SquareRootUnique(a * b, p);
}

/* helper modified by LLM (iteration 5): absolute value square equality */
lemma AbsSquare(x: real)
  ensures Abs(x) * Abs(x) == x * x
{
  if x >= 0.0 {
    assert Abs(x) == x;
    assert Abs(x) * Abs(x) == x * x;
  } else {
    assert Abs(x) == -x;
    assert Abs(x) * Abs(x) == (-x) * (-x);
    assert (-x) * (-x) == x * x;
  }
}

/* helper modified by LLM (iteration 5): division self-cancellation */
lemma DivSelf(b: real)
  requires b != 0.0
  ensures b / b == 1.0
{
  var c := b / b;
  assert c * b == b;
  assert (c - 1.0) * b == 0.0;
  // since b != 0.0, cancellation yields c == 1.0
  assert c == 1.0;
}

/* helper modified by LLM (iteration 5): division cancellation lemma */
lemma DivCancel(a: real, b: real)
  requires b != 0.0
  ensures (a * b) / b == a
{
  var c := (a * b) / b;
  assert c * b == a * b;
  assert (c - a) * b == 0.0;
  // since b != 0.0, cancellation yields c == a
  assert c == a;
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
  /* code modified by LLM (iteration 5): construct positive square-root witnesses via nondeterministic assignment and ghost Sqrt to satisfy specification */
  var arr := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i ==> arr[k] == 1.0 / Sqrt(1.0 - x[k] * x[k])
    invariant forall k :: 0 <= k < i ==> arr[k] > 0.0
  {
    // preconditions guarantee denom > 0
    assert -1.0 < x[i] < 1.0;
    var denom := 1.0 - x[i] * x[i];
    assert denom > 0.0;
    var t := 1.0 / denom;

    // Provide a ghost witness that a nonnegative square root exists (for the nondeterministic assignment)
    ghost var s := Sqrt(t);
    assert s >= 0.0 && s * s == t;

    // Nondeterministically choose arr[i] to be any nonnegative real whose square equals t.
    // Existence is justified by the ghost witness 's' above.
    arr[i] :| arr[i] * arr[i] == t && arr[i] >= 0.0;

    // From the chosen property and uniqueness of nonnegative square root, arr[i] == Sqrt(t)
    SquareRootUnique(t, arr[i]);

    // Now relate Sqrt(t) to 1.0 / Sqrt(denom): Sqrt(t*denom) == Sqrt(t)*Sqrt(denom)
    SqrtMul(t, denom);
    // Sqrt(t*denom) == Sqrt(1.0)
    // Show Sqrt(1.0) == 1.0
    SquareRootUnique(1.0, 1.0);
    assert Sqrt(t) * Sqrt(denom) == Sqrt(1.0);
    assert Sqrt(1.0) == 1.0;

    // Sqrt(denom) > 0 because denom > 0 and Sqrt yields nonnegative root
    assert Sqrt(denom) * Sqrt(denom) == denom;
    assert denom > 0.0;
    // therefore Sqrt(denom) != 0.0
    assert Sqrt(denom) != 0.0;

    // Cancel multiplication to obtain Sqrt(t) == 1.0 / Sqrt(denom)
    DivCancel(Sqrt(t), Sqrt(denom));
    assert (Sqrt(t) * Sqrt(denom)) / Sqrt(denom) == Sqrt(t);
    assert (Sqrt(1.0)) / Sqrt(denom) == 1.0 / Sqrt(denom);
    // From Sqrt(t) * Sqrt(denom) == Sqrt(1.0) and cancellation we conclude:
    assert Sqrt(t) == 1.0 / Sqrt(denom);

    // Combine equalities: arr[i] == Sqrt(t) == 1.0 / Sqrt(denom)
    assert arr[i] == 1.0 / Sqrt(denom);
    assert arr[i] > 0.0;

    i := i + 1;
  }
  w := arr[..];
}

// </vc-code>
