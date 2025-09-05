// ======= TASK =======
// Given an integer n (n ≥ 2), calculate the minimum tax Mr. Funt must pay.
// Tax rules: For any amount x, tax is the largest proper divisor of x.
// Mr. Funt can split income n into k parts where each part ≥ 2.
// Find the minimum total tax possible across all valid splits.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int) {
    n >= 2
}

function IsPrime(k: int): bool
    requires k >= 2
{
    if k == 2 then true
    else if k % 2 == 0 then false
    else IsPrimeHelper(k, 3)
}

function IsPrimeHelper(k: int, i: int): bool
    requires k >= 3 && k % 2 == 1
    requires i >= 3 && i % 2 == 1
    decreases if i * i <= k then k - i * i else 0
{
    if i * i > k then true
    else if k % i == 0 then false
    else IsPrimeHelper(k, i + 2)
}

predicate ValidMinimumTax(n: int, tax: int)
    requires ValidInput(n)
{
    (IsPrime(n) ==> tax == 1) &&
    (!IsPrime(n) && n % 2 == 0 ==> tax == 2) &&
    (!IsPrime(n) && n % 2 == 1 && IsPrime(n - 2) ==> tax == 2) &&
    (!IsPrime(n) && n % 2 == 1 && !IsPrime(n - 2) ==> tax == 3)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else if '0' <= s[index] <= '9' then
        StringToIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else
        StringToIntHelper(s, index + 1, acc)
}

function SplitLines(s: string): seq<string>
{
    SplitLinesHelper(s, 0, [], [])
}

function SplitLinesHelper(s: string, index: int, current: seq<char>, result: seq<seq<char>>): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then
        if |current| > 0 then result + [current] else result
    else if s[index] == '\n' then
        SplitLinesHelper(s, index + 1, [], result + [current])
    else
        SplitLinesHelper(s, index + 1, current + [s[index]], result)
}

// <vc-helpers>
lemma ValidMinimumTaxImpliesValidOutput(n: int, tax: int)
    requires ValidInput(n)
    requires ValidMinimumTax(n, tax)
    ensures tax == 1 || tax == 2 || tax == 3
{
    if IsPrime(n) {
        assert tax == 1;
    } else if n % 2 == 0 {
        assert tax == 2;
    } else if n % 2 == 1 && IsPrime(n - 2) {
        assert tax == 2;
    } else {
        assert !IsPrime(n) && n % 2 == 1 && !IsPrime(n - 2);
        assert tax == 3;
    }
}

lemma StringToIntOfValidOutputIsValid(output: string)
    requires output == "1" || output == "2" || output == "3"
    ensures StringToInt(output) == 1 || StringToInt(output) == 2 || StringToInt(output) == 3
{
    if output == "1" {
        assert StringToInt("1") == 1;
    } else if output == "2" {
        assert StringToInt("2") == 2;
    } else {
        assert output == "3";
        assert StringToInt("3") == 3;
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires exists lines :: lines == SplitLines(input) && |lines| > 0
    requires ValidInput(StringToInt(SplitLines(input)[0]))
    ensures output == "1" || output == "2" || output == "3"
    ensures var n := StringToInt(SplitLines(input)[0]);
            ValidMinimumTax(n, StringToInt(output))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var n := StringToInt(lines[0]);

    if IsPrime(n) {
        output := "1";
        ValidMinimumTaxImpliesValidOutput(n, 1);
        StringToIntOfValidOutputIsValid(output);
    } else if n % 2 == 0 {
        output := "2";
        ValidMinimumTaxImpliesValidOutput(n, 2);
        StringToIntOfValidOutputIsValid(output);
    } else {
        if IsPrime(n - 2) {
            output := "2";
            ValidMinimumTaxImpliesValidOutput(n, 2);
            StringToIntOfValidOutputIsValid(output);
        } else {
            output := "3";
            ValidMinimumTaxImpliesValidOutput(n, 3);
            StringToIntOfValidOutputIsValid(output);
        }
    }
}
// </vc-code>

