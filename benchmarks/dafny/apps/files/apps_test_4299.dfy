Given a positive integer N (1 ≤ N ≤ 999), determine the pronunciation of the Japanese counter word "本" 
based on the ones digit of N. The pronunciation rules are: "hon" for ones digits 2,4,5,7,9; 
"pon" for ones digits 0,1,6,8; and "bon" for ones digit 3.

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

method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures result == CorrectPronunciation(N)
{
    var ones_digit := N % 10;
    if IsHonDigit(ones_digit) {
        result := "hon\n";
    } else if IsPonDigit(ones_digit) {
        result := "pon\n";
    } else {
        result := "bon\n";
    }
}
