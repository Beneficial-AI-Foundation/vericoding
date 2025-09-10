predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    (forall i :: 0 <= i < |input|-1 ==> '0' <= input[i] <= '9') &&
    (input[0] != '0' || |input| == 2)
}

function MaxDivisibleBy3Segments(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures MaxDivisibleBy3Segments(s) >= 0
    ensures MaxDivisibleBy3Segments(s) <= |s|
{
    MaxDivisibleBy3SegmentsHelper(s, 0, "", 0)
}

// <vc-helpers>
function MaxDivisibleBy3SegmentsHelper(s: string, index: int, current: string, best: int): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
    requires 0 <= best <= index
    ensures 0 <= MaxDivisibleBy3SegmentsHelper(s, index, current, best) <= |s|
    decreases |s| - index
{
    if index == |s| then
        best
    else if |current| > 0 && StringToInt(current) % 3 == 0 && |current| > best then
        MaxDivisibleBy3SegmentsHelper(s, index + 1, current + [s[index]], |current|)
    else
        MaxDivisibleBy3SegmentsHelper(s, index + 1, current + [s[index]], best)
}

function StringToInt(s: string): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        s[0] as int - '0' as int
    else
        (s[0] as int - '0' as int) * pow10(|s| - 1) + StringToInt(s[1..])
}

function pow10(n: nat): int
    ensures pow10(n) >= 1
    decreases n
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 1
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
    if n < 10 then
        [('0' as int + n) as char]
    else
        IntToString(n / 10) + [('0' as int + n % 10) as char]
}

lemma IntToStringLemma(n: int)
    requires n >= 0
{
}

lemma MaxDivisibleBy3ContainsValidDigits(s: string, index: int, current: string, best: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists count :: 0 <= count <= |input|-1 && result == IntToString(count) + "\n"
    ensures exists count :: count == MaxDivisibleBy3Segments(input[0..|input|-1]) && result == IntToString(count) + "\n"
// </vc-spec>
// <vc-code>
{
    var trimmed_input := input[0..|input|-1];
    var count := MaxDivisibleBy3Segments(trimmed_input);
    result := IntToString(count) + "\n";
}
// </vc-code>

