predicate ValidInput(a: int, b: int, c: int)
{
    1 <= b <= a <= 20 && 1 <= c <= 20
}

function RemainingWater(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    if remaining >= 0 then remaining else 0
}

// <vc-helpers>
function SplitOnSpaces(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitOnSpaces(s)| ==> |SplitOnSpaces(s)[i]| > 0
{
    var i := 0;
    while i < |s| && s[i] == ' '
        decreases |s| - i
    {
        i := i + 1;
    }
    if i == |s| then
        []
    else
        var j := i;
        while j < |s| && s[j] != ' '
            decreases |s| - j
        {
            j := j + 1;
        }
        [s[i..j]] + SplitOnSpaces(s[j..])
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    if s == "" then
        0
    else
        var res := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant res >= 0
            invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
            decreases |s| - i
        {
            res := res * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        res
}

function power(base: int, exp: int): int
    requires base >= 0 || exp == 0
    requires exp >= 0
    ensures power(base, exp) >= 0
{
    if exp == 0 then
        1
    else
        base * power(base, exp - 1)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then
        "0"
    else
        var s := "";
        var temp_n := n;
        while temp_n > 0
            invariant temp_n >= 0
            decreases temp_n
        {
            s := (((temp_n % 10) as char) + '0') as string + s;
            temp_n := temp_n / 10;
        }
        s
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
            var parts := SplitOnSpaces(trimmed);
            var a := StringToInt(parts[0]);
            var b := StringToInt(parts[1]);
            var c := StringToInt(parts[2]);
            result == IntToString(RemainingWater(a, b, c)) + "\n"
// </vc-spec>
// <vc-code>
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpaces(trimmed);

    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);

    var remaining := RemainingWater(a, b, c);
    result := IntToString(remaining) + "\n";
}
// </vc-code>

