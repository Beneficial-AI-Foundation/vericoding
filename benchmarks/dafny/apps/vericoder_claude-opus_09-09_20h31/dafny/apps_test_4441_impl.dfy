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
method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesFunc(s)
{
    lines := [];
    var current := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant SplitLinesFuncHelper(s, i, current, lines) == SplitLinesFunc(s)
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    
    if current != "" {
        lines := lines + [current];
    }
}

method ParseInt(s: string) returns (n: int)
    ensures n == StringToInt(s)
{
    n := 0;
    var negative := false;
    var i := 0;
    
    if |s| > 0 && s[0] == '-' {
        negative := true;
        i := 1;
    }
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant negative ==> i >= 1
        invariant negative ==> |s| > 0 && s[0] == '-'
        invariant !negative ==> n == StringToIntHelper(s[..i])
        invariant negative ==> n == StringToIntHelper(s[1..i])
    {
        var digit := s[i] as int - '0' as int;
        n := n * 10 + digit;
        i := i + 1;
        assert !negative ==> s[..i] == s[..i-1] + [s[i-1]];
        assert negative ==> s[1..i] == s[1..i-1] + [s[i-1]];
    }
    
    if negative {
        n := -n;
    }
    assert negative ==> s[1..i] == s[1..];
    assert !negative ==> s[..i] == s;
}

method ConvertIntToString(n: int) returns (s: string)
    ensures s == IntToString(n)
{
    if n == 0 {
        s := "0";
    } else if n < 0 {
        var positiveStr := ConvertPositiveIntToString(-n);
        s := "-" + positiveStr;
    } else {
        s := ConvertPositiveIntToString(n);
    }
}

method ConvertPositiveIntToString(n: int) returns (s: string)
    requires n > 0
    ensures s == IntToStringHelper(n)
{
    s := "";
    var num := n;
    var originalN := n;
    
    // Build string from right to left
    while num > 0
        invariant 0 <= num <= originalN
        invariant num == 0 ==> s == IntToStringHelper(originalN)
        invariant num > 0 ==> exists k :: k >= 0 && originalN == num * Pow10(k) + (originalN % Pow10(k)) && 
                                          s == IntToStringHelperForSuffix(originalN % Pow10(k), k)
        decreases num
    {
        var digit := num % 10;
        s := [(digit + '0' as int) as char] + s;
        num := num / 10;
    }
    
    assert num == 0;
}

// Helper function for power of 10
function Pow10(k: nat): nat
{
    if k == 0 then 1 else 10 * Pow10(k-1)
}

// Helper function to generate string for a suffix
function IntToStringHelperForSuffix(n: int, k: nat): string
    requires n >= 0
    requires n < Pow10(k)
    decreases k
{
    if k == 0 then ""
    else IntToStringHelperForSuffix(n / 10, k-1) + [(n % 10 + '0' as int) as char]
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
    
    if |lines| >= 1 {
        var n := ParseInt(lines[0]);
        
        if n == 1 {
            result := "Hello World\n";
        } else if n != 1 && |lines| >= 3 {
            var a := ParseInt(lines[1]);
            var b := ParseInt(lines[2]);
            var sum := a + b;
            var sumStr := ConvertIntToString(sum);
            result := sumStr + "\n";
        } else {
            result := "";
        }
    } else {
        result := "";
    }
}
// </vc-code>

