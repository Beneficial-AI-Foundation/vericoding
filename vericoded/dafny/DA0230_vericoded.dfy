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
    } else if 12 < n < 30 {
        result := "NO";
    } else if 69 < n < 80 {
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
}
// </vc-code>

