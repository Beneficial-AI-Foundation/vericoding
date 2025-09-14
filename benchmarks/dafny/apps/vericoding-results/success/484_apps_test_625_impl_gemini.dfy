function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

// <vc-helpers>
lemma AlternatingSumProperty(n: int)
    requires n > 0
    ensures n % 2 == 0 ==> AlternatingSum(n) == n / 2
    ensures n % 2 != 0 ==> AlternatingSum(n) == n / 2 - n
    decreases n
{
    if n > 1 {
        AlternatingSumProperty(n-1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
// </vc-spec>
// <vc-code>
{
    if n % 2 == 0 {
        result := n / 2;
    } else {
        result := n / 2 - n;
    }
    AlternatingSumProperty(n);
}
// </vc-code>

