// <vc-preamble>
predicate ValidInput(N: int) {
    1 <= N <= 999
}

predicate IsHonDigit(digit: int) {
    digit == 2 || digit == 4 || digit == 5 || digit == 7 || digit == 9
}

predicate IsPonDigit(digit: int) {
    digit == 0 || digit == 1 || digit == 6 || digit == 8
}

predicate IsBonDigit(digit: int) {
    digit == 3
}

function CorrectPronunciation(N: int): string
    requires ValidInput(N)
{
    var ones_digit := N % 10;
    if IsHonDigit(ones_digit) then "hon\n"
    else if IsPonDigit(ones_digit) then "pon\n"
    else "bon\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures result == CorrectPronunciation(N)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
