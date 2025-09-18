// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
    result := true;
    var firstElement := a[0];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result == (forall j :: 0 <= j < i ==> a[j] == firstElement)
    {
        if a[i] != firstElement {
            result := false;
            break;
        }
        i := i + 1;
    }
}
// </vc-code>
