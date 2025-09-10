predicate ValidInput(s: string)
{
    |s| >= 3 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidAbbreviation(s: string, result: string)
{
    |result| >= 3 &&
    |s| >= 3 &&
    result[0] == s[0] &&
    result[|result|-1] == s[|s|-1] &&
    result == [s[0]] + IntToString(|s| - 2) + [s[|s|-1]]
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}

// <vc-helpers>
function IntToStringNat(n: nat): string
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function Concat(c: char): string
{
    c as string
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidAbbreviation(s, result)
// </vc-spec>
// <vc-code>
{
    var len := |s>;
    var middle := IntToStringNat((len - 2) as nat);
    result := Concat(s[0]) + middle + Concat(s[len - 1]);
}
// </vc-code>

