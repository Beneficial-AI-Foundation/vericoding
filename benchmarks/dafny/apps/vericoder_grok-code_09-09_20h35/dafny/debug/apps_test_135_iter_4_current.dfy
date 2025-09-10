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
// No updates needed to helpers
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures result == "Yes\n" <==> AllRemaindersDistinct(n, k)
    ensures result == "No\n" <==> HasNonDistinctRemainder(n, k)
// </vc-spec>
// <vc-code>
{
    result := "Yes\n";
    for i := 1 to k
        invariant 1 <= i <= k + 1
        invariant result == "Yes\n" || result == "No\n"
        invariant forall j :: 1 <= j < i ==> n % j == j - 1
        invariant result == "No\n" ==> n % i != i - 1
    {
        if n % i != i - 1 {
            result := "No\n";
            break;
        }
    }
}
// </vc-code>

