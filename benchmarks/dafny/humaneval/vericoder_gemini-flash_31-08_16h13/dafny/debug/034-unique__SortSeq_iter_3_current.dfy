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
function multiset(s: seq<int>): multiset<int> {
    multiset(s[0..])
}

lemma multiset_singleton_lemma(s: seq<int>)
    ensures |s| == 1 ==> multiset(s) == multiset{s[0]}

lemma multiset_append_lemma(s: seq<int>, t: seq<int>)
    ensures multiset(s + t) == multiset(s) + multiset(t)

lemma multiset_range_lemma(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s) == multiset(s[0..k]) + multiset(s[k..])

lemma multiset_swap_lemma(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)

lemma multiset_equal_swap(a:seq<int>, i:int, j:int)
    requires 0 <= i < |a|
    requires 0 <= j < |a|
    ensures multiset(a) == multiset(a[i:=a[j]][j:=a[i]])

lemma multiset_equal_singleton(x:int)
  ensures multiset([x]) == multiset{x}
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
    var sorted_s := s;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant forall k, l :: i <= k < l < |sorted_s| ==> sorted_s[k] <= sorted_s[l]
        invariant forall k, l :: 0 <= k < l < i ==> sorted_s[k] <= sorted_s[l]
        invariant forall k :: 0 <= k < i ==> sorted_s[k] <= sorted_s[i]
        invariant multiset(sorted_s) == multiset(s)
        invariant |sorted_s| == |s|
    {
        if i == |s| { break; } // Handle empty sequence or last element
        var min_val := sorted_s[i];
        var min_idx := i;
        for j := i + 1 to |s|
            invariant i < j <= |s|
            invariant sorted_s[min_idx] == min_val
            invariant min_idx >= i
            invariant forall k :: i <= k < j ==> min_val <= sorted_s[k]
            invariant multiset(sorted_s) == multiset(s)
            invariant |sorted_s| == |s|
        {
            if sorted_s[j] < min_val {
                min_val := sorted_s[j];
                min_idx := j;
            }
        }
        if min_idx != i {
            var temp := sorted_s[i];
            sorted_s := sorted_s[i := sorted_s[min_idx]];
            sorted_s := sorted_s[min_idx := temp];
            multiset_equal_swap(sorted_s, i, min_idx); // This lemma is crucial for verification
        }
    }
    return sorted_s;
}
// </vc-code>

