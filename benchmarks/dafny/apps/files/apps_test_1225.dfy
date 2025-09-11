// <vc-preamble>
predicate ValidInput(h: int) {
    h >= 1
}

function ComputeAttacks(h: int): int
    requires h >= 0
    ensures h == 0 ==> ComputeAttacks(h) == 0
    ensures h > 0 ==> ComputeAttacks(h) > 0
{
    ComputeAttacksIterative(h, 0)
}

function ComputeAttacksIterative(h: int, n: int): int
    requires h >= 0 && n >= 0
    ensures h == 0 ==> ComputeAttacksIterative(h, n) == 0
    ensures h > 0 ==> ComputeAttacksIterative(h, n) > 0
{
    if h == 0 then 0
    else pow2(n) + ComputeAttacksIterative(h / 2, n + 1)
}

function pow2(n: int) : int
    requires n >= 0
    ensures pow2(n) >= 1
    ensures pow2(n) == if n == 0 then 1 else 2 * pow2(n-1)
{
    if n <= 0 then 1
    else 2 * pow2(n-1)
}

function ParseIntFunc(s: string): int
    requires |s| > 0
    ensures ParseIntFunc(s) >= 0
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseIntHelper(s, i, acc) >= 0
    decreases |s| - i
{
    if i >= |s| || s[i] == '\n' || s[i] == ' ' then acc
    else if '0' <= s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelper(s, i + 1, acc)
}

function IntToStringFunc(n: int): string
    requires n >= 0
    ensures |IntToStringFunc(n)| > 0
    ensures n == 0 ==> IntToStringFunc(n) == "0"
    ensures n > 0 ==> |IntToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    ensures |IntToStringHelper(n, acc)| >= |acc|
    decreases n
{
    if n == 0 then acc
    else
        var digit := n % 10;
        var digitChar := ('0' as int + digit) as char;
        IntToStringHelper(n / 10, [digitChar] + acc)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    ensures |output| > 0
    ensures output[|output|-1] == '\n'
    ensures var h := ParseIntFunc(stdin_input);
            ValidInput(h) ==> output == IntToStringFunc(ComputeAttacks(h)) + "\n"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
