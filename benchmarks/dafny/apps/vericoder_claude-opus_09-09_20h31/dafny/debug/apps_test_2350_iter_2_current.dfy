predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidTestCase(x1: int, y1: int, x2: int, y2: int)
{
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

function CountDifferentSums(x1: int, y1: int, x2: int, y2: int): int
    requires ValidTestCase(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}

// <vc-helpers>
method ParseInt(s: string, start: int) returns (value: int, nextPos: int)
    requires 0 <= start <= |s|
    ensures start <= nextPos <= |s|
{
    var i := start;
    while i < |s| && s[i] == ' '
        invariant start <= i <= |s|
    {
        i := i + 1;
    }
    
    if i >= |s| {
        return 0, i;
    }
    
    var isNegative := false;
    if s[i] == '-' {
        isNegative := true;
        i := i + 1;
    }
    
    var num := 0;
    while i < |s| && '0' <= s[i] <= '9'
        invariant start <= i <= |s|
    {
        num := num * 10 + (s[i] - '0') as int;
        i := i + 1;
    }
    
    if isNegative {
        value := -num;
    } else {
        value := num;
    }
    nextPos := i;
}

method IntToString(n: int) returns (s: string)
    ensures |s| > 0
{
    if n == 0 {
        return "0";
    }
    
    var isNegative := n < 0;
    var num := if n < 0 then -n else n;
    var digits := "";
    
    while num > 0
        invariant num >= 0
        invariant num == 0 ==> |digits| > 0
    {
        var digit := (num % 10) as char + '0';
        digits := [digit] + digits;
        num := num / 10;
    }
    
    if |digits| == 0 {
        s := "0";
    } else if isNegative {
        s := "-" + digits;
    } else {
        s := digits;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures |output| >= 0
// </vc-spec>
// <vc-code>
{
    var pos := 0;
    var x1, pos1 := ParseInt(input, pos);
    var y1, pos2 := ParseInt(input, pos1);
    var x2, pos3 := ParseInt(input, pos2);
    var y2, pos4 := ParseInt(input, pos3);
    
    if ValidTestCase(x1, y1, x2, y2) {
        var result := CountDifferentSums(x1, y1, x2, y2);
        output := IntToString(result);
    } else {
        output := "0";
    }
}
// </vc-code>

