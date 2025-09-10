predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

predicate AllRemaindersDistinct(n: int, k: int)
    requires ValidInput(n, k)
{
    forall i :: 1 <= i <= k ==> n % i == (i - 1)
}

predicate HasNonDistinctRemainder(n: int, k: int)
    requires ValidInput(n, k)
{
    exists i :: 1 <= i <= k && n % i != (i - 1)
}

// <vc-helpers>
lemma AllRemaindersMutuallyExclusive(n: int, k: int)
    requires ValidInput(n, k)
    ensures AllRemaindersDistinct(n, k) <==> !HasNonDistinctRemainder(n, k)
{
    if AllRemaindersDistinct(n, k) {
        assert forall i :: 1 <= i <= k ==> n % i == (i - 1);
        if HasNonDistinctRemainder(n, k) {
            var j :| 1 <= j <= k && n % j != (j - 1);
            assert n % j == (j - 1);
            assert n % j != (j - 1);
            assert false;
        }
    }
    
    if !HasNonDistinctRemainder(n, k) {
        assert !(exists i :: 1 <= i <= k && n % i != (i - 1));
        assert forall i :: 1 <= i <= k ==> !(n % i != (i - 1));
        assert forall i :: 1 <= i <= k ==> n % i == (i - 1);
        assert AllRemaindersDistinct(n, k);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures result == "Yes\n" <==> AllRemaindersDistinct(n, k)
    ensures result == "No\n" <==> HasNonDistinctRemainder(n, k)
// </vc-spec>
// <vc-code>
{
    var i := 1;
    while i <= k
        invariant 1 <= i <= k + 1
        invariant forall j :: 1 <= j < i ==> n % j == (j - 1)
    {
        if n % i != (i - 1) {
            assert HasNonDistinctRemainder(n, k);
            AllRemaindersMutuallyExclusive(n, k);
            return "No\n";
        }
        i := i + 1;
    }
    
    assert forall j :: 1 <= j <= k ==> n % j == (j - 1);
    assert AllRemaindersDistinct(n, k);
    AllRemaindersMutuallyExclusive(n, k);
    return "Yes\n";
}
// </vc-code>

