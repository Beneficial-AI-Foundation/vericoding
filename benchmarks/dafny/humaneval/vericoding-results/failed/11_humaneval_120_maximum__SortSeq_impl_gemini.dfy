// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed Insert to function method and added lemma about sortedness */
predicate IsSorted(s: seq<int>) {
  |s| <= 1 || (s[0] <= s[1] && IsSorted(s[1..]))
}

lemma IsSortedIsTransitive(s: seq<int>)
  requires IsSorted(s)
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  decreases |s|
{
  if |s| >= 2 {
    IsSortedIsTransitive(s[1..]);
  }
}

function method Insert(x: int, s: seq<int>): (res: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(res)
  ensures |res| == |s| + 1
  ensures multiset(res) == multiset(s) + multiset{x}
{
  if |s| == 0 {
    res := [x];
  } else if x <= s[0] {
    res := [x] + s;
  } else {
    var rest_inserted := Insert(x, s[1..]);
    res := [s[0]] + rest_inserted;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added lemma call to prove final sortedness */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant IsSorted(sorted)
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := Insert(s[i], sorted);
    i := i + 1;
  }
  IsSortedIsTransitive(sorted);
}
// </vc-code>
