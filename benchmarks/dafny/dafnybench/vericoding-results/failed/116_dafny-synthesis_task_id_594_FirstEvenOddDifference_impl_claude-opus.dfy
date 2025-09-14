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
    var firstEven := -1;
    var firstOdd := -1;
    var i := 0;
    
    // Find first even number
    while i < a.Length && firstEven == -1
        invariant 0 <= i <= a.Length
        invariant firstEven == -1 || (0 <= firstEven < a.Length && IsEven(a[firstEven]))
        invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> IsOdd(a[k])
        invariant firstEven != -1 ==> forall k :: 0 <= k < firstEven ==> IsOdd(a[k])
    {
        if IsEven(a[i]) {
            firstEven := i;
        }
        i := i + 1;
    }
    
    i := 0;
    
    // Find first odd number
    while i < a.Length && firstOdd == -1
        invariant 0 <= i <= a.Length
        invariant firstOdd == -1 || (0 <= firstOdd < a.Length && IsOdd(a[firstOdd]))
        invariant firstOdd == -1 ==> forall k :: 0 <= k < i ==> IsEven(a[k])
        invariant firstOdd != -1 ==> forall k :: 0 <= k < firstOdd ==> IsEven(a[k])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
        }
        i := i + 1;
    }
    
    assert firstEven != -1 && firstOdd != -1;
    diff := a[firstEven] - a[firstOdd];
}
// </vc-code>

