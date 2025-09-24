// <vc-preamble>
ghost function SumOfSmallestDifferences(nums: seq<int>, numToSum: int): int
    requires |nums| >= 1
    requires 0 <= numToSum <= |nums| - 1
    requires forall i :: 0 <= i < |nums|-1 ==> nums[i] <= nums[i+1]
{
    var differences := seq(|nums|-1, i requires 0 <= i < |nums|-1 => nums[i+1] - nums[i]);
    var sortedDiffs := SortedSequence(differences);
    SumFirstN(sortedDiffs, numToSum)
}

ghost function {:axiom} SortedSequence(s: seq<int>): seq<int>
    ensures |SortedSequence(s)| == |s|
    ensures multiset(SortedSequence(s)) == multiset(s)
    ensures forall i, j :: 0 <= i < j < |SortedSequence(s)| ==> SortedSequence(s)[i] <= SortedSequence(s)[j]

ghost function SumFirstN(s: seq<int>, n: int): int
    requires 0 <= n <= |s|
    ensures n == 0 ==> SumFirstN(s, n) == 0
    ensures n > 0 ==> SumFirstN(s, n) == s[0] + SumFirstN(s[1..], n-1)
{
    if n == 0 then 0
    else s[0] + SumFirstN(s[1..], n-1)
}

predicate ValidInput(n: int, k: int, nums: seq<int>)
{
    n >= 1 && k >= 1 && k <= n && |nums| == n && 
    forall i :: 0 <= i < n-1 ==> nums[i] <= nums[i+1]
}
// </vc-preamble>

// <vc-helpers>
method SortArray(arr: array<int>, size: int)
    modifies arr
    requires 0 <= size <= arr.Length
    ensures forall i, j :: 0 <= i < j < size ==> arr[i] <= arr[j]
    ensures multiset(arr[0..size]) == old(multiset(arr[0..size]))
{
    var i := 0;
    while i < size
        invariant 0 <= i <= size
        invariant forall x, y :: 0 <= x < i && i <= y < size ==> arr[x] <= arr[y]
        invariant forall x, y :: 0 <= x < y < i ==> arr[x] <= arr[y]
        invariant multiset(arr[0..size]) == old(multiset(arr[0..size]))
    {
        var minIdx := i;
        var j := i + 1;
        while j < size
            invariant i <= minIdx < size
            invariant i < j <= size
            invariant forall x :: i <= x < j ==> arr[minIdx] <= arr[x]
            invariant multiset(arr[0..size]) == old(multiset(arr[0..size]))
        {
            if arr[j] < arr[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        if minIdx != i {
            var temp := arr[i];
            arr[i] := arr[minIdx];
            arr[minIdx] := temp;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, nums: seq<int>) returns (result: int)
    requires ValidInput(n, k, nums)
    ensures result >= 0
    ensures result == SumOfSmallestDifferences(nums, n-k)
// </vc-spec>
// <vc-code>
{
    var diff := new int[n-1];
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant forall j :: 0 <= j < i ==> diff[j] == nums[j+1] - nums[j]
        invariant forall j :: 0 <= j < i ==> diff[j] >= 0
    {
        diff[i] := nums[i+1] - nums[i];
        i := i + 1;
    }

    SortArray(diff, n-1);

    result := 0;
    i := 0;
    while i < n - k
        invariant 0 <= i <= n - k
        invariant result >= 0
        invariant result == SumFirstN(diff[0..], i)
    {
        result := result + diff[i];
        i := i + 1;
    }

    assert result == SumFirstN(diff[0..], n-k);
    var differences := seq(n-1, j requires 0 <= j < n-1 => nums[j+1] - nums[j]);
    assert diff[0..n-1] == differences;
    var sortedDiffs := SortedSequence(differences);
    assert multiset(diff[0..n-1]) == multiset(sortedDiffs);
    assert forall x, y :: 0 <= x < y < n-1 ==> diff[x] <= diff[y];
    assert diff[0..n-1] == sortedDiffs;
    assert result == SumFirstN(sortedDiffs, n-k);
}
// </vc-code>
