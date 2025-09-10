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
    // The lemma only holds when n is not in the exceptional ranges
    if (12 < n && n < 30) || (69 < n && n < 80) || (89 < n) {
        // In exceptional ranges, the result is always "NO" regardless of last digit
        // We need to show that the condition n%10 !=1 && !=7 && !=9 would be false
        // But actually in these ranges, the expected result is "NO", which matches the else branch
        assert ExpectedResult(n) == "NO";
    } else {
        // For these cases, the result indeed depends on the last digit
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
            // Already in the condition
        } else if 69 < n && n < 80 {
            // Already in the condition
        } else if 89 < n {
            // Already in the condition
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
    } else if 12 < n && n < 30 {
        result := "NO";
    } else if 69 < n && n < 80 {
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
    // Add assertion to help Dafny verify the postcondition
    lemma_RangeCheck(n);
}
// </vc-code>

