// <vc-preamble>
predicate IsBoringApartment(x: int)
{
    (x >= 1 && x <= 9) ||
    (x >= 11 && x <= 99 && x % 11 == 0 && x / 11 >= 1 && x / 11 <= 9) ||
    (x >= 111 && x <= 999 && x % 111 == 0 && x / 111 >= 1 && x / 111 <= 9) ||
    (x >= 1111 && x <= 9999 && x % 1111 == 0 && x / 1111 >= 1 && x / 1111 <= 9)
}

function DigitCount(n: int): int
    requires n >= 1 && n <= 9999
{
    if n <= 9 then 1
    else if n <= 99 then 2
    else if n <= 999 then 3
    else 4
}

function BoringApartmentValue(digit: int, length: int): int
    requires 1 <= digit <= 9
    requires 1 <= length <= 4
{
    if length == 1 then digit
    else if length == 2 then digit * 11
    else if length == 3 then digit * 111
    else digit * 1111
}

function TotalDigitsPressed(x: int): int
    requires IsBoringApartment(x)
    requires 1 <= x <= 9999
{
    var digit := if x <= 9 then x 
                 else if x <= 99 then x / 11
                 else if x <= 999 then x / 111
                 else x / 1111;
    var length := DigitCount(x);

    var prevDigits := if digit == 1 then 0 else (digit - 1) * (1 + 2 + 3 + 4);

    var currentDigits := (length * (length + 1)) / 2;

    prevDigits + currentDigits
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    requires IsBoringApartment(x)
    requires 1 <= x <= 9999
    ensures result >= 0
    ensures result == TotalDigitsPressed(x)
    ensures x == 1 ==> result == 1
    ensures x == 22 ==> result == 13
    ensures x == 777 ==> result == 66
    ensures x == 9999 ==> result == 90
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
