// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added proper lemmas for maintaining sorted property */
function IsSorted(s: seq<int>): bool {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MultisetSwap(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}

lemma BubblePreservesMax(s: seq<int>, pos: int)
    requires 0 <= pos < |s| - 1
    requires forall k :: pos < k < |s| - 1 ==> s[k] <= s[k + 1]
    requires s[pos] <= s[pos + 1]
    ensures forall k :: pos <= k < |s| - 1 ==> s[k] <= s[k + 1]
{
}

lemma MaxElementBubbles(s: seq<int>, start: int, end: int)
    requires 0 <= start < end < |s|
    requires forall k :: start <= k < end ==> s[k] <= s[end]
    ensures forall k :: start <= k <= end ==> s[k] <= s[end]
{
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: seq<int>) returns (result: seq<int>)
    ensures |result| == |a|
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    ensures multiset(a) == multiset(result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): simplified invariants and fixed bubble property maintenance */
    if |a| <= 1 {
        return a;
    }
    
    result := a;
    var n := |result|;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant |result| == |a|
        invariant multiset(result) == multiset(a)
        invariant forall k :: n - i <= k < |result| ==> forall l :: 0 <= l <= k ==> result[l] <= result[k]
    {
        var j := 0;
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant |result| == |a|
            invariant multiset(result) == multiset(a)
            invariant forall k :: n - i <= k < |result| ==> forall l :: 0 <= l <= k ==> result[l] <= result[k]
            invariant j > 0 ==> forall k :: 0 <= k < j ==> result[k] <= result[j]
        {
            if result[j] > result[j + 1] {
                var temp := result[j];
                result := result[j := result[j + 1]][j + 1 := temp];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
