```vc-helpers
predicate Sorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

lemma SortedConcat(s1: SortSeqState, s2: SortSeqState)
  requires Sorted(s1)
  requires Sorted(s2)
  requires forall i :: 0 <= i < |s1| ==> forall j :: 0 <= j < |s2| ==> less_eq(s1[i], s2[j])
  ensures Sorted(s1 + s2)
{
  if |s1| == 0 {
  } else {
  }
  // Prove for any pair of indices in the concatenation
  forall i, j | 0 <= i < j < |s1| + |s2|
    ensures less_eq((s1 + s2)[i], (s1 + s2)[j])
  {
    if j < |s1| {
      // both in s1
      assert less_eq(s1[i], s1[j]);
    } else if i < |s1| && |s1| <= j {
      // i in s1, j in s2
      var jj := j - |s1|;
      assert 0 <= jj < |s2|;
      assert (s1 + s2)[i] == s1[i];
      assert (s1 + s2)[j] == s2[jj];
      assert less_eq(s1[i], s2[jj]);
    } else {
      // both in s2
      var ii := i - |s1|;
      var jj := j - |s1|;
      assert 0 <= ii < jj < |s2|;
      assert (s1 + s2)[i] == s2[ii];
      assert (s1 + s2)[j] == s2[jj];
      assert less_eq(s2[ii], s2[jj]);
    }
  }
}
```

```vc-code
{
  var p: SortSeqState := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant Sorted(p)
    invariant forall k :: 0 <= k < |p| ==> (
      var t := p[k];
      0 <= t.0 < |lst| && 0 <= t.1 < |lst[t.0]| && lst[t.0][t.1] == x && t.0 < i
    )
    invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in p
    decreases |lst| - i
  {
    var r: SortSeqState := [];
    var j := |lst[i]|;
    while j > 0
      invariant 0 <= j <= |lst[i]|
      invariant Sorted(r)
      invariant forall k :: 0 <= k < |r| ==> (
        var t := r[k];
        t.0 == i && 0 <= t.1 < |lst[i]| && lst[t.0][t.1] == x
      )
      invariant forall b :: j <= b < |lst[i]| && lst[i][b] == x ==> (i, b) in r
      decreases j
    {
      j := j - 1;
      if lst[i][j] == x {
        // Maintain sortedness of r: appending (i, j) where j decreases
        r := r + [(i, j)];
      }
    }

    // Prepare to concatenate while preserving Sorted
    // Show every element of p is <= every element of r
    if |r| > 0 {
      assert forall ii :: 0 <= ii < |p| ==> forall jj :: 0 <= jj < |r| ==>
        less_eq(p[ii], r[jj])
        by {
          var jj: int;
          assume 0 <= jj < |r|;
          var ii: int;
          assume 0 <= ii < |p|;
          var a := p[ii].0;
          var b := p[ii].1;
          var u := r[jj].0;
          var v := r[jj].1;
          assert a < i; // from invariant on p
          assert u == i; // from invariant on r
          assert a < u;
          assert less((a, b), (u, v));
          assert less_eq((a, b), (u, v));
        };
    }

    // Concatenate and maintain invariants
    assert Sorted(p);
    assert Sorted(r);
    if |r| == 0 {
      // nothing to add
    } else {
      SortedConcat(p, r);
    }
    p := p + r;

    // Update coverage invariant to include row i
    assert forall b :: 0 <= b < |lst[i]| && lst[i][b] == x ==> (i, b) in r;
    assert forall a, b :: 0 <= a < i + 1 && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in p;

    i := i + 1;
  }

  // Set result
  pos := p;
}
```