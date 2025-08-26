predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
    var firstEvenIndex := 0;
    while firstEvenIndex < a.Length && IsOdd(a[firstEvenIndex])
        invariant 0 <= firstEvenIndex <= a.Length
        invariant forall k :: 0 <= k < firstEvenIndex ==> IsOdd(a[k])
    {
        firstEvenIndex := firstEvenIndex + 1;
    }
    
    var firstOddIndex := 0;
    while firstOddIndex < a.Length && IsEven(a[firstOddIndex])
        invariant 0 <= firstOddIndex <= a.Length
        invariant forall k :: 0 <= k < firstOddIndex ==> IsEven(a[k])
    {
        firstOddIndex := firstOddIndex + 1;
    }
    
    diff := a[firstEvenIndex] - a[firstOddIndex];
}
// </vc-code>