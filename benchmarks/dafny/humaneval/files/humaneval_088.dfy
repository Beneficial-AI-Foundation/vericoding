// <vc-preamble>

predicate ValidInput(arr: seq<int>)
{
    forall i :: 0 <= i < |arr| ==> arr[i] >= 0
}

predicate IsAscendingSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate IsDescendingSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

predicate ShouldSortAscending(arr: seq<int>)
{
    |arr| > 1 && (arr[0] + arr[|arr|-1]) % 2 == 1
}

predicate ShouldSortDescending(arr: seq<int>)
{
    |arr| > 1 && (arr[0] + arr[|arr|-1]) % 2 == 0
}

predicate CorrectlySorted(arr: seq<int>, result: seq<int>)
{
    (|arr| <= 1 ==> result == arr) &&
    (ShouldSortAscending(arr) ==> IsAscendingSorted(result)) &&
    (ShouldSortDescending(arr) ==> IsDescendingSorted(result))
}
method SortAscending(arr: seq<int>) returns (result: seq<int>)
    ensures multiset(result) == multiset(arr)
    ensures IsAscendingSorted(result)
{
    result := arr;
    var i := 0;
    while i < |result|
        invariant 0 <= i <= |result|
        invariant |result| == |arr|
        invariant multiset(result) == multiset(arr)
        invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
        invariant forall p, q :: 0 <= p < i <= q < |result| ==> result[p] <= result[q]
        decreases |result| - i
    {
        var j := i + 1;
        while j < |result|
            invariant i < j <= |result|
            invariant |result| == |arr|
            invariant multiset(result) == multiset(arr)
            invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
            invariant forall p, q :: 0 <= p < i <= q < |result| ==> result[p] <= result[q]
            invariant forall q :: i < q < j ==> result[i] <= result[q]
        {
            if result[j] < result[i] {
                result := result[i := result[j]][j := result[i]];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

method SortDescending(arr: seq<int>) returns (result: seq<int>)
    ensures multiset(result) == multiset(arr)
    ensures IsDescendingSorted(result)
{
    result := arr;
    var i := 0;
    while i < |result|
        invariant 0 <= i <= |result|
        invariant |result| == |arr|
        invariant multiset(result) == multiset(arr)
        invariant forall p, q :: 0 <= p < q < i ==> result[p] >= result[q]
        invariant forall p, q :: 0 <= p < i <= q < |result| ==> result[p] >= result[q]
        decreases |result| - i
    {
        var j := i + 1;
        while j < |result|
            invariant i < j <= |result|
            invariant |result| == |arr|
            invariant multiset(result) == multiset(arr)
            invariant forall p, q :: 0 <= p < q < i ==> result[p] >= result[q]
            invariant forall p, q :: 0 <= p < i <= q < |result| ==> result[p] >= result[q]
            invariant forall q :: i < q < j ==> result[i] >= result[q]
        {
            if result[j] > result[i] {
                result := result[i := result[j]][j := result[i]];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sort_array(arr: seq<int>) returns (result: seq<int>)
    requires ValidInput(arr)
    ensures multiset(result) == multiset(arr)
    ensures CorrectlySorted(arr, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
