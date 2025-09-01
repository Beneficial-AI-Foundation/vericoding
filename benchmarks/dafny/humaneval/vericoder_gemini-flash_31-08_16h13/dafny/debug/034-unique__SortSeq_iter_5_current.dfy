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
function multiset_from_seq(s: seq<int>): multiset<int> {
    multiset(s[0..])
}

lemma multiset_singleton_lemma(s: seq<int>)
    ensures |s| == 1 ==> multiset_from_seq(s) == multiset{s[0]}
{
}

lemma multiset_append_lemma(s: seq<int>, t: seq<int>)
    ensures multiset_from_seq(s + t) == multiset_from_seq(s) + multiset_from_seq(t)
{
}

lemma multiset_range_lemma(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    ensures multiset_from_seq(s) == multiset_from_seq(s[0..k]) + multiset_from_seq(s[k..])
{
}

lemma multiset_swap_lemma(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures multiset_from_seq(s[i := s[j]][j := s[i]]) == multiset_from_seq(s)
{
}

lemma multiset_equal_swap(a:seq<int>, i:int, j:int)
    requires 0 <= i < |a|
    requires 0 <= j < |a|
    ensures multiset_from_seq(a) == multiset_from_seq(a[i:=a[j]][j:=a[i]])
{
  multiset_swap_lemma(a, i, j);
}

lemma multiset_equal_singleton(x:int)
  ensures multiset_from_seq([x]) == multiset{x}
{
}
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
        invariant forall k, l :: 0 <= k < l < i ==> sorted_s[k] <= sorted_s[l]
        invariant forall k :: 0 <= k < i && i < |sorted_s| ==> sorted_s[k] <= sorted_s[i]
        invariant multiset_from_seq(sorted_s) == multiset_from_seq(s)
        invariant |sorted_s| == |s|
    {
        if i == |s| { break; } 
        var min_val := sorted_s[i];
        var min_idx := i;
        for j := i + 1 to |s|
            invariant i < j <= |s|
            invariant min_idx >= i && min_idx < j
            invariant sorted_s[min_idx] == min_val
            invariant forall k :: i <= k < j ==> min_val <= sorted_s[k]
            invariant multiset_from_seq(sorted_s) == multiset_from_seq(s)
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
        }
    }
    return sorted_s;
}
// </vc-code>

