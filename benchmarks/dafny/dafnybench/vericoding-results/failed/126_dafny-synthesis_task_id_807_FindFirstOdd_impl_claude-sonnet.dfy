predicate IsOdd(x: int)
{
    x % 2 != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
// </vc-spec>
// <vc-code>
{
    found := false;
    index := 0;
    
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant forall i :: 0 <= i < index ==> !IsOdd(a[i])
        invariant !found
    {
        if IsOdd(a[index]) {
            found := true;
            return;
        }
        index := index + 1;
    }
}
// </vc-code>

