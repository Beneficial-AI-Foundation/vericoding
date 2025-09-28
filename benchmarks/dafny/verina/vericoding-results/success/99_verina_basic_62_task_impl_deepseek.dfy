// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma FindHelper(a: array<int>, key: int, pos: int)
    requires pos >= 0
    requires pos <= a.Length
    requires forall i :: 0 <= i < pos ==> a[i] != key
    ensures (pos < a.Length && a[pos] == key) ==> a[pos] == key && forall i :: 0 <= i < pos ==> a[i] != key
    ensures pos == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
    // This lemma helps with the verification of the forall postconditions
}
// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (result: int)
    ensures
        (result == -1 || (result >= 0 && result < a.Length)) &&
        (result != -1 ==> (a[result] == key && forall i :: 0 <= i < result ==> a[i] != key)) &&
        (result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != key
    {
        if a[i] == key {
            result := i;
            return;
        }
        i := i + 1;
    }
    result := -1;
}
// </vc-code>
