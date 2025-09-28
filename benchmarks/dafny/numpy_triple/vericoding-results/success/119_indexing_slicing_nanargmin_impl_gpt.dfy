// <vc-preamble>
// Custom datatype to represent floating point values that can be NaN
datatype Float = NaN | Real(value: real)

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float)
{
    f.NaN?
}

// Predicate to check if a Float is not NaN
predicate IsReal(f: Float)
{
    f.Real?
}

// Function to extract real value (only valid for Real values)
function GetReal(f: Float): real
  requires IsReal(f)
{
  f.value
}

// Comparison function for Float values (NaN is not comparable)
predicate FloatLessOrEqual(x: Float, y: Float)
  requires IsReal(x) && IsReal(y)
{
  GetReal(x) <= GetReal(y)
}

// Method that returns the index of the minimum value ignoring NaN values
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed preconditions from predicate and included bounds inside the predicate body; strengthened lemmas with explicit index-range assertions to avoid out-of-range errors */
predicate BestIndexPrefix(a: array<Float>, hi: int, b: int)
  reads a
{
  0 <= hi <= a.Length &&
  0 <= b < hi &&
  IsReal(a[b]) &&
  (forall j :: 0 <= j < hi && IsReal(a[j]) ==> GetReal(a[b]) <= GetReal(a[j])) &&
  (forall j :: 0 <= j < b && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[b]))
}

lemma LtTrans(x: real, y: real, z: real)
  requires x < y && y < z
  ensures x < z
{}

lemma LtLeTrans(x: real, y: real, z: real)
  requires x < y && y <= z
  ensures x < z
{}

lemma InitBestAtFirstReal(a: array<Float>, i: int)
  requires 0 <= i < a.Length
  requires IsReal(a[i])
  requires forall j :: 0 <= j < i ==> !IsReal(a[j])
  ensures BestIndexPrefix(a, i + 1, i)
{
  // Minimality over prefix [0..i]
  forall j | 0 <= j && j < i + 1 && IsReal(a[j])
    ensures GetReal(a[i]) <= GetReal(a[j])
  {
    assert 0 <= j < a.Length;
    if j < i {
      // impossible, since no real entries before i
    } else {
      assert j == i;
    }
  }
  // Strictly greater for all earlier real indices (vacuous since none are real)
  forall j | 0 <= j && j < i && IsReal(a[j])
    ensures GetReal(a[j]) > GetReal(a[i])
  {
  }
}

lemma UpdateBestWhenNewSmaller(a: array<Float>, i: int, bOld: int)
  requires 0 <= i < a.Length
  requires BestIndexPrefix(a, i, bOld)
  requires IsReal(a[i])
  requires GetReal(a[i]) < GetReal(a[bOld])
  ensures BestIndexPrefix(a, i + 1, i)
{
  assert 0 <= bOld < i;
  assert 0 <= bOld < a.Length;
  assert i < a.Length;
  assert IsReal(a[bOld]);

  // Minimality over [0..i] with new best at i
  forall j | 0 <= j && j < i + 1 && IsReal(a[j])
    ensures GetReal(a[i]) <= GetReal(a[j])
  {
    assert 0 <= j < a.Length;
    if j < i {
      assert 0 <= j < i;
      assert IsReal(a[j]);
      // From BestIndexPrefix: a[bOld] <= a[j]
      assert (forall k :: 0 <= k < i && IsReal(a[k]) ==> GetReal(a[bOld]) <= GetReal(a[k]));
      assert GetReal(a[bOld]) <= GetReal(a[j]);
      LtLeTrans(GetReal(a[i]), GetReal(a[bOld]), GetReal(a[j]));
    } else {
      assert j == i;
    }
  }
  // Strictly greater for all earlier real indices
  forall j | 0 <= j && j < i && IsReal(a[j])
    ensures GetReal(a[j]) > GetReal(a[i])
  {
    assert 0 <= j < i;
    assert 0 <= j < a.Length;
    assert IsReal(a[j]);
    if j < bOld {
      // From BestIndexPrefix: for j < bOld, a[j] > a[bOld]
      assert (forall k :: 0 <= k < bOld && IsReal(a[k]) ==> GetReal(a[k]) > GetReal(a[bOld]));
      assert GetReal(a[j]) > GetReal(a[bOld]);
      LtTrans(GetReal(a[i]), GetReal(a[bOld]), GetReal(a[j]));
    } else {
      // From BestIndexPrefix: a[bOld] <= a[j]
      assert (forall k :: 0 <= k < i && IsReal(a[k]) ==> GetReal(a[bOld]) <= GetReal(a[k]));
      assert GetReal(a[bOld]) <= GetReal(a[j]);
      LtLeTrans(GetReal(a[i]), GetReal(a[bOld]), GetReal(a[j]));
    }
  }
}

lemma KeepBestWhenNewNotBetter(a: array<Float>, i: int, b: int)
  requires 0 <= i < a.Length
  requires BestIndexPrefix(a, i, b)
  requires IsReal(a[i]) ==> GetReal(a[b]) <= GetReal(a[i])
  ensures BestIndexPrefix(a, i + 1, b)
{
  assert 0 <= b < i;
  assert 0 <= b < a.Length;
  // Minimality holds for all j in [0..i]
  forall j | 0 <= j && j < i + 1 && IsReal(a[j])
    ensures GetReal(a[b]) <= GetReal(a[j])
  {
    assert 0 <= j < a.Length;
    if j < i {
      // From previous BestIndexPrefix
      assert (forall k :: 0 <= k < i && IsReal(a[k]) ==> GetReal(a[b]) <= GetReal(a[k]));
      assert GetReal(a[b]) <= GetReal(a[j]);
    } else {
      assert j == i;
      assert IsReal(a[j]);
      assert IsReal(a[i]);
      // Use the precondition when a[i] is real
      assert GetReal(a[b]) <= GetReal(a[i]);
    }
  }
  // Strict earlier indices remain strictly greater
  forall j | 0 <= j && j < b && IsReal(a[j])
    ensures GetReal(a[j]) > GetReal(a[b])
  {
    assert 0 <= j < b;
    assert 0 <= j < a.Length;
    assert IsReal(a[j]);
    assert (forall k :: 0 <= k < b && IsReal(a[k]) ==> GetReal(a[k]) > GetReal(a[b]));
    assert GetReal(a[j]) > GetReal(a[b]);
  }
}
// </vc-helpers>

// <vc-spec>
method nanargmin(a: array<Float>) returns (idx: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsReal(a[i])
  ensures 0 <= idx < a.Length
  ensures IsReal(a[idx])
  ensures forall j :: 0 <= j < a.Length && IsReal(a[j]) ==> FloatLessOrEqual(a[idx], a[j])
  ensures forall j :: 0 <= j < idx && IsReal(a[j]) ==> GetReal(a[j]) > GetReal(a[idx])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): switched BestIndexPrefix to a pure predicate without preconditions and tightened loop invariants; simplified NaN branch */
  var i := 0;
  var seen := false;
  var best := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant (!seen ==> forall j :: 0 <= j < i ==> !IsReal(a[j]))
    invariant (!seen ==> exists k :: i <= k < a.Length && IsReal(a[k]))
    invariant (seen ==> BestIndexPrefix(a, i, best))
    decreases a.Length - i
  {
    if IsReal(a[i]) {
      if !seen {
        InitBestAtFirstReal(a, i);
        seen := true;
        best := i;
      } else {
        assert BestIndexPrefix(a, i, best);
        assert IsReal(a[best]);
        if GetReal(a[i]) < GetReal(a[best]) {
          UpdateBestWhenNewSmaller(a, i, best);
          best := i;
        } else {
          assert GetReal(a[best]) <= GetReal(a[i]);
          KeepBestWhenNewNotBetter(a, i, best);
        }
      }
    } else {
      if seen {
        KeepBestWhenNewNotBetter(a, i, best);
      }
    }
    i := i + 1;
  }
  // From existence invariant, seen must be true at the end
  assert seen;
  assert BestIndexPrefix(a, i, best);
  idx := best;
}

// </vc-code>
