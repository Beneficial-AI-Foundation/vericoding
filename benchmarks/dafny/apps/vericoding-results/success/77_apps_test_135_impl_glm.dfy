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
lemma AllDistinctOrHasNonDistinct(n: int, k: int)
    requires ValidInput(n, k)
    ensures AllRemaindersDistinct(n, k) || HasNonDistinctRemainder(n, k)
{
    if !AllRemaindersDistinct(n, k) {
        calc {
            !forall i :: 1 <= i <= k ==> n % i == (i - 1);
            == 
                exists i :: 1 <= i <= k && !(n % i == (i - 1));
            == 
                exists i :: 1 <= i <= k && n % i != (i - 1);
        }
        assert HasNonDistinctRemainder(n, k);
    }
}

 lemma QuotientRemainderTheorem(x: int, y: int) returns (q: int, r: int)
    requires 0 < y
    ensures 0 <= r < y
    ensures x == q * y + r
{
    q := x / y;
    r := x % y;
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
    if AllRemaindersDistinct(n, k) {
        return "Yes\n";
    } else {
        AllDistinctOrHasNonDistinct(n, k);
        return "No\n";
    }
}
// </vc-code>

