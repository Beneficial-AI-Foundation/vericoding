// <vc-preamble>
predicate ValidInput(a: int, b: int, k: int) {
    1 <= a <= b <= 1000000000 && 1 <= k <= 100
}

function KSmallestEnd(a: int, b: int, k: int): int
    requires a <= b && k >= 1
{
    if b < a + k - 1 then b else a + k - 1
}

function KLargestStart(a: int, b: int, k: int): int
    requires a <= b && k >= 1
{
    if b - k + 1 > a + k then b - k + 1 else a + k
}

predicate IsAscendingSorted(s: seq<int>) {
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllInRange(s: seq<int>, a: int, b: int) {
    forall x :: x in s ==> a <= x <= b
}

predicate ContainsKSmallest(s: seq<int>, a: int, b: int, k: int)
    requires a <= b && k >= 1
{
    var end := KSmallestEnd(a, b, k);
    forall x :: a <= x <= end ==> x in s
}

predicate ContainsKLargest(s: seq<int>, a: int, b: int, k: int)
    requires a <= b && k >= 1
{
    var start := KLargestStart(a, b, k);
    forall x :: start <= x <= b ==> x in s
}

predicate OnlyKSmallestAndLargest(s: seq<int>, a: int, b: int, k: int)
    requires a <= b && k >= 1
{
    var smallestEnd := KSmallestEnd(a, b, k);
    var largestStart := KLargestStart(a, b, k);
    forall x :: x in s ==> (a <= x <= smallestEnd) || (largestStart <= x <= b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, k: int) returns (result: seq<int>)
    requires ValidInput(a, b, k)
    ensures |result| <= 2 * k
    ensures IsAscendingSorted(result)
    ensures AllInRange(result, a, b)
    ensures ContainsKSmallest(result, a, b, k)
    ensures ContainsKLargest(result, a, b, k)
    ensures OnlyKSmallestAndLargest(result, a, b, k)
// </vc-spec>
// <vc-code>
{
    var first_end := KSmallestEnd(a, b, k);
    var second_start := KLargestStart(a, b, k);

    var first_range: seq<int> := [];
    var i := a;
    while i <= first_end
        invariant a <= i <= first_end + 1
        invariant |first_range| == i - a
        invariant forall j :: 0 <= j < |first_range| ==> first_range[j] == a + j
        invariant forall x :: a <= x < i ==> x in first_range
    {
        first_range := first_range + [i];
        i := i + 1;
    }

    var second_range: seq<int> := [];
    if second_start <= b {
        i := second_start;
        while i <= b
            invariant second_start <= i <= b + 1
            invariant |second_range| == i - second_start
            invariant forall j :: 0 <= j < |second_range| ==> second_range[j] == second_start + j
            invariant forall x :: second_start <= x < i ==> x in second_range
        {
            second_range := second_range + [i];
            i := i + 1;
        }
    }

    result := first_range + second_range;
}
// </vc-code>
