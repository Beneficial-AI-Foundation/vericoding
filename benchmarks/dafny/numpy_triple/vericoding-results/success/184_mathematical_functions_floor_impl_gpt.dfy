// <vc-preamble>
/*
 * Implementation of numpy.floor functionality - returns the floor of each input element.
 * The floor of a real number x is the largest integer i such that i <= x.
 */

// Method that computes the floor of each element in a sequence
// Ghost predicate to check if a real number represents an integer
ghost predicate IsInteger(r: real)
{
  exists k: int {:trigger k as real} :: r == k as real
}

// Floor function (Dafny built-in)
function Floor(r: real): real
{
  r.Floor as real
}

// Ceiling function (Dafny built-in)
function Ceiling(r: real): real
{
  (-((-r).Floor)) as real
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bounds and integrality of floor */
lemma FloorBounds(r: real)
  ensures Floor(r) <= r < Floor(r) + 1.0
  ensures IsInteger(Floor(r))
{
  var i := r.Floor;
  assert Floor(r) == i as real;
  assert (i as real) <= r < (i as real) + 1.0;
  assert Floor(r) <= r < Floor(r) + 1.0;
  // witness for IsInteger(Floor(r))
  assert IsInteger(Floor(r)) by {
    var k := i;
    assert Floor(r) == k as real;
  }
}

/* helper modified by LLM (iteration 5): largest-integer property for floor */
lemma FloorLargestInteger(r: real, k: real)
  requires IsInteger(k)
  ensures Floor(r) < k ==> r < k
{
  if Floor(r) < k {
    var i := r.Floor;
    var m: int :| k == m as real;
    FloorBounds(r);
    assert Floor(r) == i as real;
    assert (i as real) < k;
    assert (i as real) < (m as real);
    assert i < m;
    assert i + 1 <= m;
    assert r < (i as real) + 1.0;
    assert ((i + 1) as real) <= (m as real);
    assert r < k;
  }
}

/* helper modified by LLM (iteration 5): integer below real implies <= floor */
lemma IntegerBelowRealLeqFloor(r: real, k: real)
  requires IsInteger(k)
  ensures k <= r ==> k <= Floor(r)
{
  if k <= r {
    if Floor(r) < k {
      FloorLargestInteger(r, k);
      // Now r < k contradicts k <= r
      assert false;
    }
    assert k <= Floor(r);
  }
}

/* helper modified by LLM (iteration 5): monotonicity of floor */
lemma FloorMonotone(r1: real, r2: real)
  ensures r1 <= r2 ==> Floor(r1) <= Floor(r2)
{
  if r1 <= r2 {
    var i1 := r1.Floor;
    var i2 := r2.Floor;
    FloorBounds(r1);
    FloorBounds(r2);
    assert IsInteger(i1 as real) by {
      var k := i1;
      assert (i1 as real) == k as real;
    }
    assert (i1 as real) <= r1;
    assert r1 <= r2;
    assert (i1 as real) <= r2;
    IntegerBelowRealLeqFloor(r2, i1 as real);
    assert (i1 as real) <= Floor(r2);
    assert Floor(r1) == i1 as real;
    assert Floor(r1) <= Floor(r2);
  }
}

/* helper modified by LLM (iteration 5): floor of an integer is itself */
lemma FloorOfInteger(r: real)
  requires IsInteger(r)
  ensures Floor(r) == r
{
  var m: int :| r == m as real;
  var i := r.Floor;
  FloorBounds(r);
  assert Floor(r) == i as real;
  assert (i as real) <= r < (i as real) + 1.0;
  assert r == m as real;
  assert (m as real) < (m as real) + 1.0;
  assert r < (m as real) + 1.0;
  assert (i as real) <= (m as real);
  assert i <= m;
  assert (m as real) < (i as real) + 1.0;
  assert m < i + 1;
  assert m <= i;
  assert i == m;
  assert Floor(r) == r;
}

/* helper modified by LLM (iteration 5): relation between floor and ceiling */
lemma FloorCeilingEq(r: real)
  ensures Floor(r) == -Ceiling(-r)
{
  assert Ceiling(-r) == (-(r.Floor)) as real;
  assert -Ceiling(-r) == -((-(r.Floor)) as real);
  assert -((-(r.Floor)) as real) == (r.Floor) as real;
  assert Floor(r) == (r.Floor) as real;
}
// </vc-helpers>

// <vc-spec>
method NumpyFloor(x: seq<real>) returns (result: seq<real>)
  // No preconditions - floor is defined for all real numbers
  ensures |result| == |x|
  // Each result element is the floor of the corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == Floor(x[i])
  // Floor properties: result[i] <= x[i] and x[i] < result[i] + 1
  ensures forall i :: 0 <= i < |x| ==> result[i] <= x[i] < result[i] + 1.0
  // Result elements are integers (represented as reals)
  ensures forall i :: 0 <= i < |x| ==> IsInteger(result[i])
  // Largest integer property: no integer k exists such that result[i] < k <= x[i]
  ensures forall i :: 0 <= i < |x| ==> 
    forall k :: IsInteger(k) && result[i] < k ==> x[i] < k
  // Monotonicity: if x[i] <= x[j] then result[i] <= result[j]
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] <= x[j] ==> 
    result[i] <= result[j]
  // Integer preservation: if x[i] is an integer, then result[i] = x[i]
  ensures forall i :: 0 <= i < |x| && IsInteger(x[i]) ==> result[i] == x[i]
  // Relationship with ceiling: result[i] = -ceiling(-x[i])
  ensures forall i :: 0 <= i < |x| ==> result[i] == -Ceiling(-x[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct result via loop and prove properties with helper lemmas */
  var n := |x|;
  result := x;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == |x|
    invariant forall j :: 0 <= j < i ==> result[j] == Floor(x[j])
    invariant forall j :: i <= j < n ==> result[j] == x[j]
    decreases n - i
  {
    result := result[i := Floor(x[i])];
    i := i + 1;
  }

  // Prove per-element equality with floor
  forall i | 0 <= i < n
    ensures result[i] == Floor(x[i])
  {
    assert result[i] == Floor(x[i]);
  }

  // Floor bounds and integrality
  forall i | 0 <= i < n
    ensures result[i] <= x[i] < result[i] + 1.0
  {
    FloorBounds(x[i]);
    assert result[i] == Floor(x[i]);
  }

  forall i | 0 <= i < n
    ensures IsInteger(result[i])
  {
    FloorBounds(x[i]);
    assert result[i] == Floor(x[i]);
  }

  // Largest-integer property
  forall i | 0 <= i < n
    ensures forall k :: IsInteger(k) && result[i] < k ==> x[i] < k
  {
    forall k | IsInteger(k) && result[i] < k
      ensures x[i] < k
    {
      assert result[i] == Floor(x[i]);
      FloorLargestInteger(x[i], k);
    }
  }

  // Monotonicity across indices
  forall i, j | 0 <= i < n && 0 <= j < n && x[i] <= x[j]
    ensures result[i] <= result[j]
  {
    assert result[i] == Floor(x[i]);
    assert result[j] == Floor(x[j]);
    FloorMonotone(x[i], x[j]);
  }

  // Integer preservation
  forall i | 0 <= i < n && IsInteger(x[i])
    ensures result[i] == x[i]
  {
    assert result[i] == Floor(x[i]);
    FloorOfInteger(x[i]);
  }

  // Relation to ceiling
  forall i | 0 <= i < n
    ensures result[i] == -Ceiling(-x[i])
  {
    assert result[i] == Floor(x[i]);
    FloorCeilingEq(x[i]);
  }
}

// </vc-code>
