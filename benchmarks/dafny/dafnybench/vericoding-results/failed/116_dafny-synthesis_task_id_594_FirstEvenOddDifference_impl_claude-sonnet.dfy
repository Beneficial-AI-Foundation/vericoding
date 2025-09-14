predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
method ComputeFirstEven(a: array<int>) returns (firstEven: int)
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    ensures 0 <= firstEven < a.Length
    ensures IsEven(a[firstEven])
    ensures forall k :: 0 <= k < firstEven ==> IsOdd(a[k])
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    {
        if IsEven(a[i]) {
            firstEven := i;
            return;
        }
        i := i + 1;
    }
}

method ComputeFirstOdd(a: array<int>) returns (firstOdd: int)
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures 0 <= firstOdd < a.Length
    ensures IsOdd(a[firstOdd])
    ensures forall k :: 0 <= k < firstOdd ==> IsEven(a[k])
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> IsEven(a[k])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            return;
        }
        i := i + 1;
    }
}
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
    var firstEven := ComputeFirstEven(a);
    var firstOdd := ComputeFirstOdd(a);
    diff := a[firstEven] - a[firstOdd];
}
// </vc-code>

