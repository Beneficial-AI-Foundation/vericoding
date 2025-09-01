method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function seq_of<T>(s: set<T>): seq<T>
  ensures |seq_of(s)| == |s|
  ensures forall e :: e in s <==> e in seq_of(s)
{
  if s == {} then [] else ([s.Any] + seq_of(s - {s.Any}))
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| <= 1 then
    return s;
  else
    var pivot := s[0];
    var smaller_elements := new set<int>();
    var larger_elements := new set<int>();
    for k := 1 to |s| - 1
    {
      if s[k] <= pivot then
        smaller_elements := smaller_elements + {s[k]};
      else
        larger_elements := larger_elements + {s[k]};
    }
    var smaller := SortSeq(seq_of(smaller_elements));
    var larger := SortSeq(seq_of(larger_elements));
    return smaller + [pivot] + larger;
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rev_s: seq<int> := [];
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant |rev_s| == |s| - (i + 1)
    invariant forall k :: 0 <= k < |rev_s| ==> rev_s[k] == s[|s| - 1 - k]
  {
    rev_s := rev_s + [s[i]];
    i := i - 1;
  }
  return rev_s;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}