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
{
    var firstEvenIndex := 0;
    var firstOddIndex := 0;
    
    // Find first even number
    while firstEvenIndex < a.Length && !IsEven(a[firstEvenIndex])
        invariant 0 <= firstEvenIndex <= a.Length
        invariant forall k :: 0 <= k < firstEvenIndex ==> IsOdd(a[k])
    {
        firstEvenIndex := firstEvenIndex + 1;
    }
    
    // Find first odd number
    while firstOddIndex < a.Length && !IsOdd(a[firstOddIndex])
        invariant 0 <= firstOddIndex <= a.Length
        invariant forall k :: 0 <= k < firstOddIndex ==> IsEven(a[k])
    {
        firstOddIndex := firstOddIndex + 1;
    }
    
    result := a[firstEvenIndex] - a[firstOddIndex];
}
// </vc-code>
