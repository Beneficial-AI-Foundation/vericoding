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
    var i: int := 0;
    while i < a.Length && !IsEven(a[i])
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
        invariant exists k :: i <= k < a.Length && IsEven(a[k])
    {
        i := i + 1;
    }
    var j: int := 0;
    while j < a.Length && !IsOdd(a[j])
        invariant 0 <= j <= a.Length
        invariant forall k :: 0 <= k < j ==> IsEven(a[k])
        invariant exists k :: j <= k < a.Length && IsOdd(a[k])
    {
        j := j + 1;
    }
    return a[i] - a[j];
}
// </vc-code>

