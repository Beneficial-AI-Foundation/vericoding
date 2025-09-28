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
    var firstEvenIndex := -1;
    var firstOddIndex := -1;
    
    var i := 0;
    while i < a.Length && (firstEvenIndex == -1 || firstOddIndex == -1)
        invariant 0 <= i <= a.Length
        invariant firstEvenIndex == -1 ==> (forall k :: 0 <= k < i ==> IsOdd(a[k]))
        invariant firstEvenIndex != -1 ==> 0 <= firstEvenIndex < i && IsEven(a[firstEvenIndex]) && (forall k :: 0 <= k < firstEvenIndex ==> IsOdd(a[k]))
        invariant firstOddIndex == -1 ==> (forall k :: 0 <= k < i ==> IsEven(a[k]))
        invariant firstOddIndex != -1 ==> 0 <= firstOddIndex < i && IsOdd(a[firstOddIndex]) && (forall k :: 0 <= k < firstOddIndex ==> IsEven(a[k]))
    {
        if firstEvenIndex == -1 && IsEven(a[i]) {
            firstEvenIndex := i;
        }
        if firstOddIndex == -1 && IsOdd(a[i]) {
            firstOddIndex := i;
        }
        i := i + 1;
    }
    
    result := a[firstEvenIndex] - a[firstOddIndex];
}
// </vc-code>
