method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function MultisetEq<T>(s1: seq<T>, s2: seq<T>): bool
{
  multiset(s1) == multiset(s2)
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
   if |s| == 0 {
    return [];
   }
   var sorted_s := SortSeq(s);
  var strange_s := new int[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i && k % 2 == 0 ==> strange_s[k] == sorted_s[k / 2]
    invariant forall k :: 0 <= k < i && k % 2 == 1 ==> strange_s[k] == sorted_s[|s| - (k - 1) / 2 - 1]
    invariant forall k :: i <= k < |s| ==> strange_s[k] == 0 // Elements beyond i are default initialized (0)
    invariant MultisetEq(s, sorted_s) // Add this line
    invariant |strange_s| == |s|
    invariant |sorted_s| == |s|
  {
    if i % 2 == 0 {
      strange_s[i] := sorted_s[i / 2];
    } else {
      strange_s[i] := sorted_s[|s| - (i - 1) / 2 - 1];
    }
    i := i + 1;
  }
  return strange_s[..];
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