// <vc-preamble>
// Helper predicate to check if two sequences are permutations of each other
predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  |a| == |b| &&
  (forall i :: 0 <= i < |a| ==> exists j :: 0 <= j < |b| && a[i] == b[j]) &&
  (forall j :: 0 <= j < |b| ==> exists i :: 0 <= i < |a| && b[j] == a[i])
}

// Helper predicate to check if a sequence is sorted in non-decreasing order
predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Method to compute the median of a non-empty sequence of real numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove element at index i from sequence */
function RemoveAt(s: seq<real>, i: nat): seq<real>
  requires 0 <= i < |s|
{
  s[..i] + s[i+1..]
}

/* helper modified by LLM (iteration 5): compute index of minimal element (recursive function) */
function MinIndex(s: seq<real>): nat
  requires |s| >= 1
  decreases |s|
  ensures 0 <= result < |s|
  ensures forall k :: 0 <= k < |s| ==> s[result] <= s[k]
{
  if |s| == 1 then 0
  else let r := MinIndex(s[1..]) in if s[0] <= s[1 + r] then 0 else 1 + r
}

lemma RemoveAtPermutation(s: seq<real>, i: nat)
  requires 0 <= i < |s|
  ensures IsPermutation(s, [s[i]] + RemoveAt(s, i))
{
  assert |s| == |[s[i]] + RemoveAt(s, i)|;

  forall p | 0 <= p < |s|
  {
    if p == i {
      var q := 0;
      assert 0 <= q < |[s[i]] + RemoveAt(s, i)|;
      assert s[p] == ([s[i]] + RemoveAt(s, i))[q];
      assert exists q' :: 0 <= q' < |[s[i]] + RemoveAt(s, i)| && s[p] == ([s[i]] + RemoveAt(s, i))[q'];
    } else if p < i {
      var q := p + 1;
      assert 0 <= q < |[s[i]] + RemoveAt(s, i)|;
      assert s[p] == ([s[i]] + RemoveAt(s, i))[q];
      assert exists q' :: 0 <= q' < |[s[i]] + RemoveAt(s, i)| && s[p] == ([s[i]] + RemoveAt(s, i))[q'];
    } else {
      var q := p;
      assert 0 <= q < |[s[i]] + RemoveAt(s, i)|;
      assert ([s[i]] + RemoveAt(s, i))[q] == RemoveAt(s, i)[q - 1];
      assert RemoveAt(s, i)[q - 1] == s[p];
      assert exists q' :: 0 <= q' < |[s[i]] + RemoveAt(s, i)| && s[p] == ([s[i]] + RemoveAt(s, i))[q'];
    }
  }

  forall q | 0 <= q < |[s[i]] + RemoveAt(s, i)|
  {
    if q == 0 {
      var p := i;
      assert 0 <= p < |s|;
      assert ([s[i]] + RemoveAt(s, i))[q] == s[p];
      assert exists p' :: 0 <= p' < |s| && ([s[i]] + RemoveAt(s, i))[q] == s[p'];
    } else {
      if q - 1 < i {
        assert RemoveAt(s, i)[q - 1] == s[q - 1];
        assert ([s[i]] + RemoveAt(s, i))[q] == s[q - 1];
        assert exists p' :: 0 <= p' < |s| && ([s[i]] + RemoveAt(s, i))[q] == s[p'];
      } else {
        assert RemoveAt(s, i)[q - 1] == s[q];
        assert ([s[i]] + RemoveAt(s, i))[q] == s[q];
        assert exists p' :: 0 <= p' < |s| && ([s[i]] + RemoveAt(s, i))[q] == s[p'];
      }
    }
  }
}

lemma ConcatPreservesPermutation(p: seq<real>, x: seq<real>, y: seq<real>)
  requires IsPermutation(x, y)
  ensures IsPermutation(p + x, p + y)
{
  assert |p + x| == |p| + |x|;
  assert |p + y| == |p| + |y|;
  assert |x| == |y|;

  forall r | 0 <= r < |p + x|
  {
    if r < |p| {
      var q := r;
      assert (p + x)[r] == p[q];
      assert exists s' :: 0 <= s' < |p + y| && (p + x)[r] == (p + y)[s'];
    } else {
      var rx := r - |p|;
      assert 0 <= rx < |x|;
      assert (forall i :: 0 <= i < |x| ==> exists j :: 0 <= j < |y| && x[i] == y[j]);
      assert exists sy :: 0 <= sy < |y| && x[rx] == y[sy];
      assert exists s' :: 0 <= s' < |p + y| && (p + x)[r] == (p + y)[s'];
    }
  }

  forall r | 0 <= r < |p + y|
  {
    if r < |p| {
      assert exists s' :: 0 <= s' < |p + x| && (p + y)[r] == (p + x)[s'];
    } else {
      var ry := r - |p|;
      assert 0 <= ry < |y|;
      assert (forall j :: 0 <= j < |y| ==> exists i :: 0 <= i < |x| && y[j] == x[i]);
      assert exists s' :: 0 <= s' < |p + x| && (p + y)[r] == (p + x)[s'];
    }
  }
}

lemma PermutationTransitive(x: seq<real>, y: seq<real>, z: seq<real>)
  requires IsPermutation(x, y) && IsPermutation(y, z)
  ensures IsPermutation(x, z)
{
  assert |x| == |y|;
  assert |y| == |z|;

  forall i | 0 <= i < |x|
  {
    assert exists j :: 0 <= j < |y| && x[i] == y[j];
    var j :| 0 <= j < |y| && x[i] == y[j];
    assert exists k :: 0 <= k < |z| && y[j] == z[k];
    var k :| 0 <= k < |z| && y[j] == z[k];
    assert x[i] == z[k];
    assert exists k' :: 0 <= k' < |z| && x[i] == z[k'];
  }

  forall i | 0 <= i < |z|
  {
    assert exists j :: 0 <= j < |y| && z[i] == y[j];
    var j :| 0 <= j < |y| && z[i] == y[j];
    assert exists k :: 0 <= k < |x| && y[j] == x[k];
    var k :| 0 <= k < |x| && y[j] == x[k];
    assert z[i] == x[k];
    assert exists k' :: 0 <= k' < |x| && z[i] == x[k'];
  }
}

// </vc-helpers>

// <vc-spec>
method median(a: seq<real>) returns (m: real)
  requires |a| >= 1
  ensures exists sorted: seq<real> ::
    // sorted is a permutation of the input sequence a
    IsPermutation(a, sorted) &&
    // sorted is in non-decreasing order
    IsSorted(sorted) &&
    // m is computed correctly based on whether the length is odd or even
    (if |sorted| % 2 == 1 then
      // odd case: middle element at index |sorted| / 2
      m == sorted[|sorted| / 2]
    else
      // even case: average of the two middle elements
      m == (sorted[|sorted| / 2 - 1] + sorted[|sorted| / 2]) / 2.0
    ) &&
    // median property: m is either an element from the sorted sequence,
    // or the average of two elements from the sorted sequence
    ((exists i :: 0 <= i < |sorted| && m == sorted[i]) ||
    (exists i, j :: (0 <= i < |sorted| && 0 <= j < |sorted| && 
                     m == (sorted[i] + sorted[j]) / 2.0)))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): selection-sort-like construction of sorted sequence with permutation transitivity */
  var remaining := a;
  var sorted: seq<real> := [];

  while |remaining| > 0
    invariant IsPermutation(a, sorted + remaining)
    invariant IsSorted(sorted)
    invariant forall i, j :: 0 <= i < |sorted| && 0 <= j < |remaining| ==> sorted[i] <= remaining[j]
    decreases |remaining|
  {
    var idx := MinIndex(remaining);
    var v := remaining[idx];

    assert 0 <= idx < |remaining|;
    assert forall j :: 0 <= j < |remaining| ==> remaining[idx] <= remaining[j];

    var oldSorted := sorted;
    var oldRemaining := remaining;

    RemoveAtPermutation(oldRemaining, idx);
    ConcatPreservesPermutation(oldSorted, oldRemaining, [v] + RemoveAt(oldRemaining, idx));
    PermutationTransitive(a, oldSorted + oldRemaining, oldSorted + ([v] + RemoveAt(oldRemaining, idx)));

    sorted := oldSorted + [v];
    remaining := RemoveAt(oldRemaining, idx);

    assert forall p, q :: 0 <= p < q < |sorted| ==> sorted[p] <= sorted[q];
    assert forall i, j :: 0 <= i < |sorted| && 0 <= j < |remaining| ==> sorted[i] <= remaining[j];
    assert IsPermutation(a, sorted + remaining);
  }

  assert IsPermutation(a, sorted);
  assert IsSorted(sorted);

  if |sorted| % 2 == 1 {
    m := sorted[|sorted| / 2];
  } else {
    m := (sorted[|sorted| / 2 - 1] + sorted[|sorted| / 2]) / 2.0;
  }

}

// </vc-code>
