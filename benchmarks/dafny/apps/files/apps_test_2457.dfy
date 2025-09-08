Given n grains where each grain weighs between (a-b) and (a+b) grams inclusive,
determine if the total weight of all n grains can fall within the range [c-d, c+d] grams inclusive.
Input format: first line contains number of test cases t, followed by t lines each containing
5 integers n, a, b, c, d representing the parameters for each test case.
Output "Yes" if possible, "No" otherwise for each test case.

predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| >= 0
    ensures |lines| >= 0
    ensures forall i :: 0 <= i < |lines| ==> '\n' !in lines[i]
{
    lines := [];
    var start := 0;
    var i := 0;

    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant forall j :: 0 <= j < |lines| ==> '\n' !in lines[j]
        invariant forall k :: start <= k < i ==> s[k] != '\n'
    {
        if s[i] == '\n' {
            if start < i {
                var line := s[start..i];
                lines := lines + [line];
            }
            start := i + 1;
        }
        i := i + 1;
    }

    if start < |s| {
        var line := s[start..];
        lines := lines + [line];
    }
}

method SplitSpaces(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> ' ' !in parts[i]
{
    parts := [];
    var start := 0;
    var i := 0;

    while i <= |s|
        invariant 0 <= start <= i <= |s| + 1
        invariant forall j :: 0 <= j < |parts| ==> ' ' !in parts[j]
        invariant i <= |s| ==> forall k :: start <= k < i ==> s[k] != ' '
    {
        if i == |s| || s[i] == ' ' {
            if start < i {
                var part := s[start..i];
                parts := parts + [part];
            }
            start := i + 1;
        }
        i := i + 1;
    }
}

method ParseInt(s: string) returns (n: int)
    requires |s| >= 0
    ensures s == "" ==> n == 0
{
    if s == "" {
        return 0;
    }

    n := 0;
    var i := 0;
    var negative := false;

    if |s| > 0 && s[0] == '-' {
        negative := true;
        i := 1;
    }

    while i < |s|
        invariant 0 <= i <= |s|
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }

    if negative {
        n := -n;
    }
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
{
    if input == "" || input == "\n" {
        return "";
    }

    var lines := SplitLines(input);
    if |lines| == 0 { return ""; }

    var t := ParseInt(lines[0]);
    if t < 0 { t := 0; }
    var output := "";

    var i := 1;
    while i <= t && i < |lines|
        invariant 1 <= i <= t + 1
        invariant i <= |lines|
        invariant t >= 0
        invariant ValidOutput(output)
        invariant |output| > 0 ==> output[|output|-1] == '\n'
    {
        var parts := SplitSpaces(lines[i]);
        if |parts| >= 5 {
            var n := ParseInt(parts[0]);
            var a := ParseInt(parts[1]);
            var b := ParseInt(parts[2]);
            var c := ParseInt(parts[3]);
            var d := ParseInt(parts[4]);

            if CanAchieveWeight(n, a, b, c, d) {
                output := output + "Yes\n";
            } else {
                output := output + "No\n";
            }
        }
        i := i + 1;
    }

    return output;
}
