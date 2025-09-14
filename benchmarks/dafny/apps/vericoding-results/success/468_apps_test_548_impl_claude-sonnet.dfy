predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
lemma AllEvenAndHasOddExclusive(a: seq<int>)
    ensures AllEven(a) <==> !HasOdd(a)
{
    if AllEven(a) {
        assert forall i :: 0 <= i < |a| ==> a[i] % 2 == 0;
        if HasOdd(a) {
            var j :| 0 <= j < |a| && a[j] % 2 == 1;
            assert a[j] % 2 == 0;
            assert false;
        }
    } else {
        assert exists i :: 0 <= i < |a| && a[i] % 2 == 1;
        var k :| 0 <= k < |a| && a[k] % 2 == 1;
        assert HasOdd(a);
    }
}

lemma ExhaustiveCase(a: seq<int>)
    ensures AllEven(a) || HasOdd(a)
{
    if !AllEven(a) {
        assert exists i :: 0 <= i < |a| && a[i] % 2 == 1;
        assert HasOdd(a);
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
    AllEvenAndHasOddExclusive(a);
    ExhaustiveCase(a);
    
    if AllEven(a) {
        result := "Second";
    } else {
        result := "First";
    }
}
// </vc-code>

