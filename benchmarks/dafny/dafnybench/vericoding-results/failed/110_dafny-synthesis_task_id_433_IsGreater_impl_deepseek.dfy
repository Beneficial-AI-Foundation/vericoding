

// <vc-helpers>
lemma ForallNotGreaterImpliesExistsNotLess(n: int, a: array<int>)
    requires a != null
    ensures !(forall i :: 0 <= i < a.Length ==> n > a[i]) 
        ==> exists i :: 0 <= i < a.Length && n <= a[i]
{
    if !(forall i :: 0 <= i < a.Length ==> n > a[i]) {
        var i :| 0 <= i < a.Length && !(n > a[i]);
        assert n <= a[i];
    }
}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// <vc-code>
{
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant forall j :: 0 <= j < index ==> n > a[j]
    {
        if n <= a[index] {
            return false;
        }
        index := index + 1;
    }
    return true;
}
// </vc-code>

