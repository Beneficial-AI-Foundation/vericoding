// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change */
lemma multiset_permutation_trans(s1: seq<int>, s2: seq<int>, s3: seq<int>)
  requires multiset(s1) == multiset(s2)
  requires multiset(s2) == multiset(s3)
  ensures multiset(s1) == multiset(s3)
{
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
/* code modified by LLM (iteration 5): The fixes apply to the nested loop invariants. The outer loop invariant now correctly specifies that the prefix of the array up to 'i' is sorted and that 'arr' contains the same elements as 's'. The inner loop invariants track the minimum element found so far and ensure the multiset property is maintained. Now it ensures that for all k, l such that i <= k < l < j, arr[min_idx] <= arr[k].*/
{
    var n := |s|;
    if n == 0 {
        return [];
    }

    var arr := new int[n];
    for k := 0 to n - 1 {
        arr[k] := s[k];
    }

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant forall k, l :: 0 <= k < l < i ==> arr[k] <= arr[l]
        invariant arr.Length == |s|
        invariant multiset(arr[..]) == multiset(s)
    {
        var min_idx := i;
        for j := i + 1 to n - 1
            invariant i <= min_idx < j
            invariant forall k :: i <= k < j ==> arr[min_idx] <= arr[k]
            invariant arr.Length == |s|
            invariant multiset(arr[..]) == multiset(s)
        {
            if arr[j] < arr[min_idx] {
                min_idx := j;
            }
        }
        if min_idx != i {
            var temp := arr[i];
            arr[i] := arr[min_idx];
            arr[min_idx] := temp;
        }
    }
    return arr[..];
}
// </vc-code>
