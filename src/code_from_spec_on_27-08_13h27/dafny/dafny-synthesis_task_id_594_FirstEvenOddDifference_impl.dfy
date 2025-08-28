predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma EvenOddExistence(a: array<int>, i: int, j: int)
    requires a.Length >= 2
    requires 0 <= i < a.Length && 0 <= j < a.Length
    requires IsEven(a[i]) && IsOdd(a[j])
    ensures exists k, m :: 0 <= k < a.Length && 0 <= m < a.Length && IsEven(a[k]) && IsOdd(a[m])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// </vc-spec>

// <vc-code>
method FirstEvenOddDifferenceImpl(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> !IsOdd(a[k]))
{
    var firstEven := -1;
    var firstOdd := -1;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> !IsEven(a[k])
        invariant firstOdd == -1 ==> forall k :: 0 <= k < i ==> !IsOdd(a[k])
        invariant firstEven != -1 ==> 0 <= firstEven < i && IsEven(a[firstEven]) && forall k :: 0 <= k < firstEven ==> !IsEven(a[k])
        invariant firstOdd != -1 ==> 0 <= firstOdd < i && IsOdd(a[firstOdd]) && forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k])
        invariant firstEven != -1 && firstOdd != -1 ==> exists k, m :: 0 <= k < a.Length && 0 <= m < a.Length && IsEven(a[k]) && IsOdd(a[m])
    {
        if IsEven(a[i]) && firstEven == -1 {
            firstEven := i;
        }
        if IsOdd(a[i]) && firstOdd == -1 {
            firstOdd := i;
        }
        if firstEven != -1 && firstOdd != -1 {
            break;
        }
        i := i + 1;
    }
    
    assert firstEven != -1 && firstOdd != -1;
    diff := a[firstEven] - a[firstOdd];
}
// </vc-code>
