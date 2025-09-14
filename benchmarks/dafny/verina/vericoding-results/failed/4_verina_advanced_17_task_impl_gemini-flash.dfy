// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed loop invariants and out of bounds access */
    result := new int[l.Length];
    if l.Length == 0 {
        return result;
    }

    for k := 0 to l.Length - 1
        invariant 0 <= k <= l.Length
        invariant forall p :: 0 <= p < k ==> result[p] == l[p]
    {
        result[k] := l[k];
    }

    for i := 1 to result.Length - 1
        invariant 1 <= i <= result.Length
        invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
        invariant multiset(result[0 .. i]) == multiset(l[0 .. i])
        invariant multiset(result[i ..]) == multiset(l[i ..])
        invariant result.Length == l.Length
        invariant forall p :: i <= p < result.Length ==> result[p] == l[p]
    {
        var x := result[i];
        var j := i - 1;
        while j >= 0 && result[j] > x
            invariant -1 <= j < i
            invariant forall k :: j < k < i ==> result[k] == l[k-(i-old(i))] // This invariant is tricky
            invariant forall k :: 0 <= k <= j ==> result[k] == old(result[k]) // This invariant is tricky too
            invariant forall k :: i < k < result.Length ==> result[k] == l[k]
            invariant multiset(result[0 .. i+1]) == multiset(old(result[0 .. i+1]))
            decreases j
        {
            result[j + 1] := result[j];
            j := j - 1;
        }
        result[j + 1] := x;
    }
}
// </vc-code>
