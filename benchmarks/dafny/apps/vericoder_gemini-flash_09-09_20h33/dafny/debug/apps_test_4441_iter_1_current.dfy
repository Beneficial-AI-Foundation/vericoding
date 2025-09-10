predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

function ExpectedOutput(stdin_input: string): string
{
    var lines := SplitLinesFunc(stdin_input);
    if |lines| >= 1 then
        var n := StringToInt(lines[0]);
        if n == 1 then "Hello World\n"
        else if n != 1 && |lines| >= 3 then
            var a := StringToInt(lines[1]);
            var b := StringToInt(lines[2]);
            IntToString(a + b) + "\n"
        else ""
    else ""
}

function SplitLinesFunc(s: string): seq<string>
{
    SplitLinesFuncHelper(s, 0, "", [])
}

function SplitLinesFuncHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if current == "" then acc else acc + [current]
    else if s[i] == '\n' then
        SplitLinesFuncHelper(s, i + 1, "", acc + [current])
    else
        SplitLinesFuncHelper(s, i + 1, current + [s[i]], acc)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
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
    else IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]
}

// <vc-helpers>
function method SplitLines(s: string): seq<string>
{
    var lines := new String[0];
    var currentLine := "";
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |lines| ==> "\n" !in lines[j]
        invariant "\n" !in currentLine
        invariant s == (Concat(lines) + currentLine + s[i..])
    {
        if i < |s| && s[i] == '\n' {
            lines := lines + [currentLine];
            currentLine := "";
        } else if i < |s| {
            currentLine := currentLine + [s[i]];
        }
    }
    if currentLine != "" || |s| == 0 then lines := lines + [currentLine];
    return lines;
}

function method Concat(s: seq<string>): string {
  if |s| == 0 then ""
  else s[0] + Concat(s[1..])
}

function method ToInt(s: string): int
{
    var res := 0;
    var sign := 1;
    var i := 0;

    if |s| > 0 && s[0] == '-' {
        sign := -1;
        i := 1;
    }

    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i && (s[k] == '-' || !('0' <= s[k] <= '9')) ==> false
        invariant (sign == 1 && res == StringToInt(s[..i])) || (sign == -1 && res == StringToInt(s[1..i]))
    {
        var digit := (s[i] as int) - ('0' as int);
        res := res * 10 + digit;
        i := i + 1;
    }
    return res * sign;
}

function method FromInt(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + FromInt(-n)
    else {
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant s == IntToStringHelper(n/int_power(10, |s|))
            decreases temp
        {
            s := [(temp % 10 + '0' as int) as char] + s;
            temp := temp / 10;
        }
        s
    }
}

function int_power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * int_power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == ExpectedOutput(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    if |lines| < 1 {
        return "";
    }
    var n_str := lines[0];
    var n := ToInt(n_str);

    if n == 1 {
        return "Hello World\n";
    } else {
        if |lines| < 3 {
            return "";
        }
        var a_str := lines[1];
        var b_str := lines[2];
        var a := ToInt(a_str);
        var b := ToInt(b_str);
        var sum := a + b;
        return FromInt(sum) + "\n";
    }
}
// </vc-code>

