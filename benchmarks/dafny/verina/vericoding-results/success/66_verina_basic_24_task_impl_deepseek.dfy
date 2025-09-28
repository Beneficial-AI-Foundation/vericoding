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
/* helper modified by LLM (iteration 4): Add termination decreases clauses to recursive functions */
function FirstEvenIndexExists(a: array<int>, low: int, high: int): (index: int)
    reads a
    requires a.Length > 0 && 0 <= low <= high < a.Length
    requires exists x :: low <= x <= high && IsEven(a[x])
    ensures low <= index <= high && IsEven(a[index])
    ensures forall k :: low <= k < index ==> IsOdd(a[k])
    decreases high - low
{
    if IsEven(a[low]) then
        low
    else
        FirstEvenIndexExists(a, low + 1, high)
}

function FirstOddIndexExists(a: array<int>, low: int, high: int): (index: int)
    reads a
    requires a.Length > 0 && 0 <= low <= high < a.Length
    requires exists x :: low <= x <= high && IsOdd(a[x])
    ensures low <= index <= high && IsOdd(a[index])
    ensures forall k :: low <= k < index ==> IsEven(a[k])
    decreases high - low
{
    if IsOdd(a[low]) then
        low
    else
        FirstOddIndexExists(a, low + 1, high)
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
/* code modified by LLM (iteration 4): No changes needed to code implementation */
{
    var firstEvenIndex: int;
    var firstOddIndex: int;
    
    firstEvenIndex := FirstEvenIndexExists(a, 0, a.Length - 1);
    firstOddIndex := FirstOddIndexExists(a, 0, a.Length - 1);
    
    result := a[firstEvenIndex] - a[firstOddIndex];
}
// </vc-code>
