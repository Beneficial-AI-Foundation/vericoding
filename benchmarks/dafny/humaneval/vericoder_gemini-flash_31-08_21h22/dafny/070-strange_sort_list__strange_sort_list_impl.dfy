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
function SeqToMultiset<T>(s: seq<T>): multiset<T> {
    if s == [] then multiset{} else multiset{s[0]} + SeqToMultiset(s[1..])
}

predicate IsSorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    ensures SeqToMultiset(s) == SeqToMultiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures IsSorted(sorted)
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
{
    sorted := SortSeq(s);

    var len := |s|;
    strange := new int[len];

    var small_idx := 0;
    var large_idx := len - 1;

    for i := 0 to len-1
        invariant 0 <= i <= len
        invariant 0 <= small_idx <= (i + 1) / 2
        invariant len - (i + 1) / 2 <= large_idx <= len
        invariant forall k :: 0 <= k < i && k % 2 == 0 ==> strange[k] == sorted[k / 2]
        invariant forall k :: 0 <= k < i && k % 2 == 1 ==> strange[k] == sorted[len - (k - 1) / 2 - 1]
    {
        if i % 2 == 0 {
            strange[i] := sorted[small_idx];
            small_idx := small_idx + 1;
        } else {
            strange[i] := sorted[large_idx];
            large_idx := large_idx - 1;
        }
    }
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
   var sorted_res: seq<int>;
   var strange_res: seq<int>;
   (sorted_res, strange_res) := strange_sort_list_helper(s);
   return strange_res;
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