method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall a, b :: 0 <= a < b < |sorted| ==> sorted[a] <= sorted[b]
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    var pos := 0;
    while pos < |sorted| && sorted[pos] <= s[i]
      invariant 0 <= pos <= |sorted|
    {
      pos := pos + 1;
    }
    sorted := sorted[..pos] + [s[i]] + sorted[pos..];
    i := i + 1;
  }
}
// </vc-code>

