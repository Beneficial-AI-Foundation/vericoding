predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result <==> forall j :: 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a[j]))
    {
        if IsOdd(i) && !IsOdd(a[i]) {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
