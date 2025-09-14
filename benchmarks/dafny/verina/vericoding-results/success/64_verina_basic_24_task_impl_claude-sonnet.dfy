// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed from array<int> to seq<int> parameter types and updated implementation to work with sequences */
function FindFirstEven(a: seq<int>): int
    requires |a| > 0
    requires exists x :: 0 <= x < |a| && IsEven(a[x])
    ensures 0 <= FindFirstEven(a) < |a|
    ensures IsEven(a[FindFirstEven(a)])
    ensures forall k :: 0 <= k < FindFirstEven(a) ==> IsOdd(a[k])
{
    if IsEven(a[0]) then 0
    else 1 + FindFirstEven(a[1..])
}

function FindFirstOdd(a: seq<int>): int
    requires |a| > 0
    requires exists x :: 0 <= x < |a| && IsOdd(a[x])
    ensures 0 <= FindFirstOdd(a) < |a|
    ensures IsOdd(a[FindFirstOdd(a)])
    ensures forall k :: 0 <= k < FindFirstOdd(a) ==> IsEven(a[k])
{
    if IsOdd(a[0]) then 0
    else 1 + FindFirstOdd(a[1..])
}
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (result: int)
    requires 
        a.Length > 1 &&
        (exists x :: 0 <= x < a.Length && IsEven(a[x])) &&
        (exists x :: 0 <= x < a.Length && IsOdd(a[x]))
    ensures 
        exists i, j :: 
            0 <= i < a.Length && 0 <= j < a.Length &&
            IsEven(a[i]) && IsOdd(a[j]) &&
            result == a[i] - a[j] &&
            (forall k :: 0 <= k < i ==> IsOdd(a[k])) &&
            (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): using iterative approach instead of helper functions to find first even and odd positions */
{
    var i := 0;
    while i < a.Length && IsOdd(a[i])
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    {
        i := i + 1;
    }
    
    var j := 0;
    while j < a.Length && IsEven(a[j])
        invariant 0 <= j <= a.Length
        invariant forall k :: 0 <= k < j ==> IsEven(a[k])
    {
        j := j + 1;
    }
    
    result := a[i] - a[j];
}
// </vc-code>
