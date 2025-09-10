predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
lemma AllEvenNotHasOdd(a: seq<int>)
    ensures AllEven(a) <==> !HasOdd(a)
{
    if AllEven(a) {
        // If all are even, then there's no odd
        assert forall i :: 0 <= i < |a| ==> a[i] % 2 == 0;
        assert !exists i :: 0 <= i < |a| && a[i] % 2 == 1;
    } else {
        // If not all are even, then there exists an odd
        assert !(forall i :: 0 <= i < |a| ==> a[i] % 2 == 0);
        assert exists i :: 0 <= i < |a| && !(a[i] % 2 == 0);
        assert exists i :: 0 <= i < |a| && a[i] % 2 == 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j] % 2 == 0
    {
        if a[i] % 2 != 0 {
            assert a[i] % 2 == 1;
            assert HasOdd(a);
            AllEvenNotHasOdd(a);
            assert !AllEven(a);
            return "First";
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j < |a| ==> a[j] % 2 == 0;
    assert AllEven(a);
    AllEvenNotHasOdd(a);
    assert !HasOdd(a);
    return "Second";
}
// </vc-code>

