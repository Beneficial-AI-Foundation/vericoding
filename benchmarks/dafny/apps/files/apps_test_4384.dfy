Given an integer N (1 ≤ N ≤ 1998), determine the first three characters of the N-th AtCoder Beginner Contest label.
Contest labeling system: Rounds 1-999 use "ABC", rounds 1000-1998 use "ABD".

predicate ValidInput(n: int) {
    1 <= n <= 1998
}

function ExpectedResult(n: int): string
    requires ValidInput(n)
{
    if n < 1000 then "ABC" else "ABD"
}

method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
{
    if n < 1000 {
        result := "ABC";
    } else {
        result := "ABD";
    }
}
