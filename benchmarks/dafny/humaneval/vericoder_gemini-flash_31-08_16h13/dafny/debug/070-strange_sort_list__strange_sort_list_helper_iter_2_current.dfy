

// <vc-helpers>
function multiset_from_seq<T>(s: seq<T>): multiset<T>
{
  multiset(s[i] | i in 0..|s|-1)
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var s_sorted := SortSeq(s);
    if |s| == 0 {
        return [], [];
    } else {
        var str := new int[|s|];
        var j := 0; // Pointer for the beginning of s_sorted
        var k := |s| - 1; // Pointer for the end of s_sorted
        
        for i := 0 to |s| - 1
            invariant 0 <= i <= |s|
            invariant 0 <= j
            invariant k <= |s| - 1
            invariant j + (|s| - k) == i
            invariant i % 2 == 0 ==> j == i / 2
            invariant i % 2 == 1 ==> (|s| - k) == (i + 1) / 2
            invariant forall idx :: 0 <= idx < i && idx % 2 == 0 ==> str[idx] == s_sorted[idx / 2]
            invariant forall idx :: 0 <= idx < i && idx % 2 == 1 ==> str[idx] == s_sorted[|s| - (idx - 1) / 2 - 1]
        {
            if i % 2 == 0 {
                str[i] := s_sorted[j];
                j := j + 1;
            } else {
                str[i] := s_sorted[k];
                k := k - 1;
            }
        }
        return s_sorted, str;
    }
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
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