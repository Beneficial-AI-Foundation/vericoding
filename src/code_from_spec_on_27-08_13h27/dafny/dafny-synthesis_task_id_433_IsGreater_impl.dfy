// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsGreaterImpl(n: int, a: array<int>) returns (result: bool)
    requires a.Length >= 0
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall k :: 0 <= k < i ==> n > a[k]
        invariant !result ==> exists k :: 0 <= k < i && n <= a[k]
    {
        if n <= a[i]
        {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
