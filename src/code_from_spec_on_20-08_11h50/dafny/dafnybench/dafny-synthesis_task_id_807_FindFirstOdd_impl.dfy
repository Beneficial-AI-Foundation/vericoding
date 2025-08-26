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
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
    {
        if IsOdd(a[i]) {
            found := true;
            index := i;
            return;
        }
        i := i + 1;
    }
    found := false;
    index := 0; // arbitrary value since found is false
}
// </vc-code>