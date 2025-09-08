Given an array of n integers where initially a[x] = 1 and all other elements are 0,
determine how many positions can contain the value 1 after performing m swap operations optimally.
Each operation i allows swapping any two elements at positions c and d where l_i ≤ c, d ≤ r_i.

predicate ValidInput(testCases: seq<(int, int, seq<(int, int)>)>)
{
    |testCases| >= 0 &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        n >= 1 && 1 <= x <= n && |operations| >= 0 &&
        (forall j :: 0 <= j < |operations| ==> 
            var (l, r) := operations[j];
            1 <= l <= r <= n)
}

function computeFinalBounds(x: int, operations: seq<(int, int)>): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
{
    computeFinalBoundsHelper(x, x, operations, 0)
}

predicate ValidResults(testCases: seq<(int, int, seq<(int, int)>)>, results: seq<int>)
    requires ValidInput(testCases)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        var finalBounds := computeFinalBounds(x, operations);
        results[i] == finalBounds.1 - finalBounds.0 + 1 &&
        finalBounds.0 <= x <= finalBounds.1 &&
        results[i] >= 1 &&
        1 <= finalBounds.0 <= finalBounds.1 <= n
}

function computeFinalBoundsHelper(left: int, right: int, operations: seq<(int, int)>, index: int): (int, int)
    requires 0 <= index <= |operations|
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    decreases |operations| - index
{
    if index >= |operations| then (left, right)
    else 
        var (l, r) := operations[index];
        var newLeft := if l < left && left <= r then l else left;
        var newRight := if r > right && right >= l then r else right;
        computeFinalBoundsHelper(newLeft, newRight, operations, index + 1)
}

method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
{
    results := [];

    for i := 0 to |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant forall k :: 0 <= k < i ==> 
            var (n, x, operations) := testCases[k];
            var finalBounds := computeFinalBounds(x, operations);
            results[k] == finalBounds.1 - finalBounds.0 + 1
        invariant forall k :: 0 <= k < i ==> 
            var (n, x, operations) := testCases[k];
            var finalBounds := computeFinalBounds(x, operations);
            finalBounds.0 <= x <= finalBounds.1
        invariant forall k :: 0 <= k < i ==> results[k] >= 1
        invariant forall k :: 0 <= k < i ==> 
            var (n, x, operations) := testCases[k];
            var finalBounds := computeFinalBounds(x, operations);
            1 <= finalBounds.0 <= finalBounds.1 <= n
    {
        var (n, x, operations) := testCases[i];

        var left := x;
        var right := x;

        for j := 0 to |operations|
            invariant 0 <= j <= |operations|
            invariant left <= x <= right
            invariant 1 <= left <= right <= n
            invariant computeFinalBounds(x, operations) == computeFinalBoundsHelper(left, right, operations, j)
        {
            var (l, r) := operations[j];

            if l < left && left <= r {
                left := l;
            }
            if r > right && right >= l {
                right := r;
            }
        }

        var answer := right - left + 1;
        results := results + [answer];
    }
}
