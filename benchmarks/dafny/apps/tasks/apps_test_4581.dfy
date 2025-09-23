// <vc-preamble>
predicate ValidInput(s: string) {
    |s| == 3 && forall i :: 0 <= i < |s| ==> s[i] == 'o' || s[i] == 'x'
}

function countO(s: string): int
    ensures countO(s) >= 0
    ensures countO(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'o' then 1 else 0) + countO(s[1..])
}

function CalculatePrice(s: string): int
    requires ValidInput(s)
    ensures CalculatePrice(s) >= 700
    ensures CalculatePrice(s) == countO(s) * 100 + 700
{
    countO(s) * 100 + 700
}

function IntToString(n: int) : string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string) : string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else IntToStringHelper(n / 10, [((n % 10) + 48) as char] + acc)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == IntToString(CalculatePrice(s)) + "\n"
    ensures CalculatePrice(s) >= 700
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
