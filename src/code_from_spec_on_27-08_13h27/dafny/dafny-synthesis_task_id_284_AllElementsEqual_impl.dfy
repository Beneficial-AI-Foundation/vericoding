// <vc-helpers>
// No helper code needed for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// </vc-spec>

// <vc-code>
method AllElementsEqualImpl(a: array<int>, n: int) returns (result: bool)
    requires a.Length >= 0
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall k :: 0 <= k < i ==> a[k] == n
        invariant !result ==> exists k :: 0 <= k < i && a[k] != n
    {
        if a[i] != n {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
