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
function method Summation(n: int): int
    requires n >= 0
    ensures Summation(n) == (n * (n + 1)) / 2
{
    if n == 0 then 0
    else n + Summation(n - 1)
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
    if n == 1 {
        return -1;
    }

    var sign := 1;
    if n % 2 != 0 {
        sign := -1;
    }

    var result_val := sign * (n / 2);

    if n % 2 != 0 {
           return -((n / 2) + n);
    } else {
        return (n / 2);
    }
}
// </vc-code>

