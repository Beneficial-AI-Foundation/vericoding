// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function CheckAllRemaindersDistinct(n: int, k: int): bool
{
    forall i :: 1 <= i <= k ==> n % i == (i - 1)
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
    if CheckAllRemaindersDistinct(n, k) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>
