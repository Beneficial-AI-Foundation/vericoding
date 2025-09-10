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
{
    if k == 0 then
        true
    else if n % k == (k - 1) then
        AllRemaindersDistinctCompute(n, k - 1)
    else
        false
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
    if AllRemaindersDistinctCompute(n, k) then
        return "Yes\n";
    else
        return "No\n";
}
// </vc-code>

