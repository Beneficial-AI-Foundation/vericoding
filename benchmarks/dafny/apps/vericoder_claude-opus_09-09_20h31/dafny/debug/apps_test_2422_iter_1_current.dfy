predicate ValidSolution(n: int, a: int, b: int, c: int)
{
    a >= 0 && b >= 0 && c >= 0 && 3 * a + 5 * b + 7 * c == n
}

predicate ValidResult(n: int, result: seq<int>)
{
    (|result| == 1 && result[0] == -1) ||
    (|result| == 3 && result[0] >= 0 && result[1] >= 0 && result[2] >= 0 && 
     ValidSolution(n, result[0], result[1], result[2]))
}

// <vc-helpers>
lemma VerifySolution(n: int, a: int, b: int, c: int)
    requires a >= 0 && b >= 0 && c >= 0
    requires 3 * a + 5 * b + 7 * c == n
    ensures ValidSolution(n, a, b, c)
{
}

lemma Case0Valid(n: int)
    requires n >= 1 && n % 3 == 0
    ensures ValidSolution(n, n / 3, 0, 0)
{
    assert 3 * (n / 3) + 5 * 0 + 7 * 0 == n;
}

lemma Case1Valid(n: int)
    requires n >= 7 && n % 3 == 1
    ensures ValidSolution(n, (n - 7) / 3, 0, 1)
{
    assert 3 * ((n - 7) / 3) + 5 * 0 + 7 * 1 == n;
}

lemma Case2Valid(n: int)
    requires n >= 5 && n % 3 == 2
    ensures ValidSolution(n, (n - 5) / 3, 1, 0)
{
    assert 3 * ((n - 5) / 3) + 5 * 1 + 7 * 0 == n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
    requires n >= 1
    ensures ValidResult(n, result)
    ensures n % 3 == 0 ==> |result| == 3 && result == [n / 3, 0, 0]
    ensures n % 3 == 1 && n < 7 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 1 && n >= 7 ==> |result| == 3 && result == [(n - 7) / 3, 0, 1]
    ensures n % 3 == 2 && n < 5 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 2 && n >= 5 ==> |result| == 3 && result == [(n - 5) / 3, 1, 0]
// </vc-spec>
// <vc-code>
{
    if n % 3 == 0 {
        Case0Valid(n);
        result := [n / 3, 0, 0];
    } else if n % 3 == 1 {
        if n < 7 {
            result := [-1];
        } else {
            Case1Valid(n);
            result := [(n - 7) / 3, 0, 1];
        }
    } else {
        assert n % 3 == 2;
        if n < 5 {
            result := [-1];
        } else {
            Case2Valid(n);
            result := [(n - 5) / 3, 1, 0];
        }
    }
}
// </vc-code>

