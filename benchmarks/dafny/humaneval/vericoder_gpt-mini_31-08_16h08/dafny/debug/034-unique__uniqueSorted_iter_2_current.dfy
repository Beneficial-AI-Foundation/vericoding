

// <vc-helpers>
// No helper lemmas needed.
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall a, b :: 0 <= a < b < |r| ==> r[a] < r[b]
    invariant forall x :: x in r ==> x in s[..i]
    invariant forall x :: x in s[..i] ==> x in r
  {
    if i == 0 || s[i] != s[i-1] {
      if |r| > 0 {
        var last := r[|r|-1];
        // last was taken from some position < i
        assert last in s[..i];
        assert exists j :: 0 <= j < i && s[j] == last;
        var j :| 0 <= j < i && s[j] == last;
        // derive s[j] <= s[i-1]
        if j < i-1 {
          // j < i-1 < |s|, so by sortedness s[j] <= s[i-1]
          assert s[j] <= s[i-1];
        } else {
          // j == i-1
          assert j == i-1;
          assert s[j] == s[i-1];
        }
        // since i>0 here, and j < i, we have 0 <= i-1 < i < |s|, so s[i-1] <= s[i]
        assert s[i-1] <= s[i];
        // and because we are in the branch s[i] != s[i-1], we get strictness
        assert s[i-1] != s[i];
        assert s[i-1] < s[i];
        // combine to get last < s[i]
        assert last <= s[i-1];
        assert last < s[i];
      }
      r := r + [s[i]];
    }
    i := i + 1;
  }
  return r;
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}