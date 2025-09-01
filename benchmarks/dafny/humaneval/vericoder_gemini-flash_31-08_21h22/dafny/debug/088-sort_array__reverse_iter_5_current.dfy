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
  ensures multiset(s) == multiset(seq_of(s))
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
    // Proof that multiset(smaller_elements) + multiset(larger_elements) + multiset({pivot}) == multiset(s) - {s[0]}
    // It's part of the partitioning logic.
    // The for loop invariant will show how elements are partitioned.
    for k := 1 to |s| - 1
      invariant multiset(s[1..k]) == multiset(smaller_elements) + multiset(larger_elements)
    {
      if s[k] <= pivot then
        smaller_elements := smaller_elements + {s[k]};
      else
        larger_elements := larger_elements + {s[k]};
    }
    var smaller := SortSeq(seq_of(smaller_elements));
    var larger := SortSeq(seq_of(larger_elements));
    // Proof that the concatenation preserves multiset equality
    // multiset(smaller) == multiset(smaller_elements)
    // multiset(larger) == multiset(larger_elements)
    // multiset(smaller) + multiset([pivot]) + multiset(larger) == multiset(smaller_elements) + multiset({pivot}) + multiset(larger_elements)
    //                                                           == multiset(s[1..|s|-1]) + multiset({s[0]})
    //                                                           == multiset(s)
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
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |rev_s| == i
    invariant forall k :: 0 <= k < i ==> rev_s[k] == s[|s| - 1 - k]
  {
    rev_s := rev_s + [s[|s| - 1 - i]];
    i := i + 1;
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