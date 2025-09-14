

// <vc-helpers>
lemma NotAllEqualImpliesExists(a: array<int>, n: int, i: int)
    requires 0 <= i <= a.Length
    requires exists j :: 0 <= j < i && a[j] != n
    ensures exists j :: 0 <= j < a.Length && a[j] != n
{
    var j :| 0 <= j < i && a[j] != n;
    assert 0 <= j < a.Length;
}

lemma AllEqualImpliesForall(a: array<int>, n: int, i: int)
    requires 0 <= i <= a.Length
    requires forall j :: 0 <= j < i ==> a[j] == n
    ensures forall j :: 0 <= j < i ==> a[j] == n
{
}
// </vc-helpers>

// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// <vc-code>
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall j :: 0 <= j < i ==> a[j] == n
        invariant !result ==> exists j :: 0 <= j < i && a[j] != n
    {
        if a[i] != n {
            result := false;
        }
        i := i + 1;
    }
    if result {
        AllEqualImpliesForall(a, n, i);
    } else {
        NotAllEqualImpliesExists(a, n, i);
    }
}
// </vc-code>

