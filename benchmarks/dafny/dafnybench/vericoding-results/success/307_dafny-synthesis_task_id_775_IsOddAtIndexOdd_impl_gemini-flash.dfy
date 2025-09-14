predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> (IsOdd(k) ==> IsOdd(a[k]))
    {
        if IsOdd(i) && !IsOdd(a[i])
        {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>

