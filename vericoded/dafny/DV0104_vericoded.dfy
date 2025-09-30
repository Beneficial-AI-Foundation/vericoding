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
    var firstEven := -1;
    var firstOdd := -1;
    var i := 0;
    
    while i < a.Length && (firstEven == -1 || firstOdd == -1)
        invariant 0 <= i <= a.Length
        invariant firstEven == -1 || (0 <= firstEven < i && IsEven(a[firstEven]))
        invariant firstOdd == -1 || (0 <= firstOdd < i && IsOdd(a[firstOdd]))
        invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> IsOdd(a[k])
        invariant firstOdd == -1 ==> forall k :: 0 <= k < i ==> IsEven(a[k])
        invariant firstEven != -1 ==> forall k :: 0 <= k < firstEven ==> IsOdd(a[k])
        invariant firstOdd != -1 ==> forall k :: 0 <= k < firstOdd ==> IsEven(a[k])
    {
        if firstEven == -1 && IsEven(a[i]) {
            firstEven := i;
        }
        if firstOdd == -1 && IsOdd(a[i]) {
            firstOdd := i;
        }
        i := i + 1;
    }
    
    result := a[firstEven] - a[firstOdd];
}
// </vc-code>
