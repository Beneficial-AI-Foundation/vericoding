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
    result := true;
    var idx := 0;
    while idx < a.Length
        invariant 0 <= idx <= a.Length
        invariant result <==> forall i :: 0 <= i < idx ==> (IsOdd(i) ==> IsOdd(a[i]))
    {
        if IsOdd(idx) && !IsOdd(a[idx]) {
            result := false;
        }
        idx := idx + 1;
    }
}
// </vc-code>

