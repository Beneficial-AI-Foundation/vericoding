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
function AllRemaindersDistinctCompute(n: int, k: int): bool
    requires ValidInput(n, k)
    decreases k
{
    if k == 0 then
        true
    else if n % k == (k - 1) then
        AllRemaindersDistinctCompute(n, k - 1)
    else
        false
}

lemma AllRemaindersDistinctCompute_implies_AllRemaindersDistinct(n: int, k: int)
    requires ValidInput(n,k)
    requires AllRemaindersDistinctCompute(n,k)
    ensures AllRemaindersDistinct(n,k)
    decreases k
{
    if k > 0 {
        assert n % k == (k-1);
        AllRemaindersDistinctCompute_implies_AllRemaindersDistinct(n,k-1);
        assert forall i :: 1 <= i < k ==> n % i == (i-1); // This line was missing an assert for the property
    }
}

lemma AllRemaindersDistinct_implies_AllRemaindersDistinctCompute(n: int, k: int)
    requires ValidInput(n,k)
    requires AllRemaindersDistinct(n,k)
    ensures AllRemainmersDistinctCompute(n,k)
    decreases k
{
    if k > 0 {
        assert n % k == (k-1);
        forall i :: 1 <= i < k ==> n % i == (i - 1) by {
            assert AllRemaindersDistinct(n,k);
        }
        AllRemaindersDistinct_implies_AllRemaindersDistinctCompute(n,k-1);
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
    AllRemaindersDistinctCompute_implies_AllRemaindersDistinct(n,k);
    AllRemaindersDistinct_implies_AllRemaindersDistinctCompute(n,k);

    if AllRemaindersDistinctCompute(n, k) then
        return "Yes\n";
    else
        return "No\n";
}
// </vc-code>

