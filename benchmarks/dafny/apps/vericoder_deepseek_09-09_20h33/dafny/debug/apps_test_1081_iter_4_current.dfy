predicate ValidInput(n: int) {
    1 <= n <= 99
}

function ExpectedResult(n: int): string
    requires ValidInput(n)
{
    if n < 12 then
        if n == 1 || n == 7 || n == 9 || n == 10 || n == 11 then "NO" else "YES"
    else if 12 < n < 30 then
        "NO"
    else if 69 < n < 80 then
        "NO"
    else if 89 < n then
        "NO"
    else
        var lastDigit := n % 10;
        if lastDigit != 1 && lastDigit != 7 && lastDigit != 9 then "YES" else "NO"
}

predicate ValidOutput(result: string) {
    result == "YES" || result == "NO"
}

// <vc-helpers>
lemma lemma_LastDigitCheck(n: int)
    requires ValidInput(n)
    requires n >= 12
    ensures ExpectedResult(n) == (if n % 10 != 1 && n % 10 != 7 && n % 10 != 9 then "YES" else "NO")
{
    if (12 < n && n < 30) || (69 < n && n < 80) || (89 < n) {
        assert ExpectedResult(n) == "NO";
    } else {
        assert ExpectedResult(n) == (if n % 10 != 1 && n % 10 != 7 && n % 10 != 9 then "YES" else "NO");
    }
}

lemma lemma_RangeCheck(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) == "NO" <==> 
        (n == 1 || n == 7 || n == 9 || n == 10 || n == 11 ||
         (12 < n && n < 30) ||
         (69 < n && n < 80) ||
         (89 < n) ||
         (n >= 12 && (n % 10 == 1 || n % 10 == 7 || n % 10 == 9)))
{
    if ExpectedResult(n) == "NO" {
        if n < 12 {
            assert n == 1 || n == 7 || n == 9 || n == 10 || n == 11;
        } else if 12 < n && n < 30 {
        } else if 69 < n && n < 80 {
        } else if 89 < n {
        } else {
            var lastDigit := n % 10;
            assert lastDigit == 1 || lastDigit == 7 || lastDigit == 9;
        }
    } else {
        assert !(n == 1 || n == 7 || n == 9 || n == 10 || n == 11 ||
                (12 < n && n < 30) ||
                (69 < n && n < 80) ||
                (89 < n));
        if n >= 12 {
            var lastDigit := n % 10;
            assert lastDigit != 1 && lastDigit != 7 && lastDigit != 9;
        }
    }
}

lemma lemma_Exact12(n: int)
    requires ValidInput(n)
    requires n == 12
    ensures ExpectedResult(n) == "YES"
{
}

lemma lemma_Exact30(n: int)
    requires ValidInput(n)
    requires n == 30
    ensures ExpectedResult(n) == "YES"
{
    assert n % 10 == 0;
}

lemma lemma_Exact69(n: int)
    requires ValidInput(n)
    requires n == 69
    ensures ExpectedResult(n) == "NO"
{
    assert n % 10 == 9;
}

lemma lemma_Exact80(n: int)
    requires ValidInput(n)
    requires n == 80
    ensures ExpectedResult(n) == "YES"
{
    assert n % 10 == 0;
}

lemma lemma_Exact89(n: int)
    requires ValidInput(n)
    requires n == 89
    ensures ExpectedResult(n) == "NO"
{
    assert n % 10 == 9;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == ExpectedResult(n)
// </vc-spec>
// <vc-code>
{
    if n < 12 {
        if n == 1 || n == 7 || n == 9 || n == 10 || n == 11 {
            result := "NO";
        } else {
            result := "YES";
        }
    } else if n == 12 {
        lemma_Exact12(n);
        result := "YES";
    } else if 12 < n && n < 30 {
        result := "NO";
    } else if n == 30 {
        lemma_Exact30(n);
        result := "YES";
    } else if n == 69 {
        lemma_Exact69(n);
        result := "NO";
    } else if 69 < n && n < 80 {
        result := "NO";
    } else if n == 80 {
        lemma_Exact80(n);
        result := "YES";
    } else if n == 89 {
        lemma_Exact89(n);
        result := "NO";
    } else if 89 < n {
        result := "NO";
    } else {
        var lastDigit := n % 10;
        if lastDigit != 1 && lastDigit != 7 && lastDigit != 9 {
            result := "YES";
        } else {
            result := "NO";
        }
    }
    lemma_RangeCheck(n);
}
// </vc-code>

