// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    (input[|input|-1] == '\n' ==> |input| > 1) &&
    (forall i :: 0 <= i < |input| ==> 
        (input[i] == '\n' || ('0' <= input[i] <= '9'))) &&
    exists j :: 0 <= j < |input| && '0' <= input[j] <= '9'
}

function ParseInteger(input: string): int
    requires ValidInput(input)
{
    ParseIntegerHelper(input, 0, 0)
}

function ParseIntegerHelper(input: string, index: int, acc: int): int
    requires 0 <= index <= |input|
    requires acc >= 0
    decreases |input| - index
{
    if index >= |input| || input[index] == '\n' then acc
    else if '0' <= input[index] <= '9' then
        ParseIntegerHelper(input, index + 1, acc * 10 + (input[index] as int - '0' as int))
    else acc
}

function FactorialMod(n: int, m: int): int
    requires n >= 0
    requires m > 0
{
    FactorialModHelper(n, m, 1, 1)
}

function FactorialModHelper(n: int, m: int, current: int, acc: int): int
    requires n >= 0
    requires m > 0
    requires current >= 1
    requires acc >= 0
    decreases n - current + 1
{
    if current > n then acc
    else FactorialModHelper(n, m, current + 1, (acc * current) % m)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n, "")
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else IntToStringHelper(n / 10, [(n % 10 + '0' as int) as char] + acc)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    requires 1 <= ParseInteger(stdin_input) <= 100000
    ensures result == IntToString(FactorialMod(ParseInteger(stdin_input), 1000000007)) + "\n"
// </vc-spec>
// <vc-code>
{
    var n := ParseInteger(stdin_input);
    var factorial_result := FactorialMod(n, 1000000007);
    result := IntToString(factorial_result) + "\n";
}
// </vc-code>
