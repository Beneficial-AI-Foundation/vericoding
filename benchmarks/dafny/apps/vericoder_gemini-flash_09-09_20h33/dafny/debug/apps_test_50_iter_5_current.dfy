predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input &&
    var lines := SplitLinesFunc(input);
    |lines| >= 3 &&
    ValidIntLine(lines[0], 3) &&
    ValidIntLine(lines[1]) &&
    ValidIntLine(lines[2]) &&
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    |firstLine| == 3 && firstLine[0] >= 1 && firstLine[1] >= 1 && firstLine[2] >= 1 &&
    |S| == firstLine[0] && |B| == firstLine[1]
}

function ParseInput(input: string): (int, int, int, seq<int>, seq<int>)
    requires ValidInput(input)
    ensures var result := ParseInput(input);
        result.0 >= 1 && result.1 >= 1 && result.2 >= 1 &&
        |result.3| == result.0 && |result.4| == result.1 &&
        (forall i :: 0 <= i < |result.3| ==> result.3[i] >= 1) &&
        (forall i :: 0 <= i < |result.4| ==> result.4[i] >= 1)
{
    var lines := SplitLinesFunc(input);
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    (firstLine[0], firstLine[1], firstLine[2], S, B)
}

function ComputeMaxBourles(r: int, S: seq<int>, B: seq<int>): int
    requires r >= 1
    requires |S| >= 1 && |B| >= 1
    requires forall i :: 0 <= i < |S| ==> S[i] >= 1
    requires forall i :: 0 <= i < |B| ==> B[i] >= 1
{
    var x := MinSeqFunc(S);
    var y := MaxSeqFunc(B);
    var cnt := (r % x) + (r / x) * y;
    if r > cnt then r else cnt
}

// <vc-helpers>
function SplitLinesFunc(input: string): seq<string>
    reads input
    ensures forall i :: 0 <= i < |SplitLinesFunc(input)| ==> |SplitLinesFunc(input)[i]| > 0
{
    var lines: seq<string> := [];
    var start := 0;
    while start < |input|
        invariant 0 <= start <= |input|
        invariant forall i :: 0 <= i < |lines| ==> |lines[i]| > 0
    {
        var newlineIndex := -1;
        var k := start;
        while k < |input|
            invariant start <= k <= |input|
            invariant forall l :: start <= l < k ==> input[l] != '\n'
        {
            if input[k] == '\n' then
                newlineIndex := k;
                break;
            k := k + 1;
        }

        if newlineIndex == -1 {
            var lastLine := input[start..];
            if |lastLine| > 0 {
                lines := lines + [lastLine];
            }
            start := |input|;
        } else {
            var line := input[start..newlineIndex];
            if |line| > 0 {
                lines := lines + [line];
            }
            start := newlineIndex + 1;
        }
    }
    lines
}

function IsDigit(c: char): bool {
  '0' <= c <= '9'
}

function StringToIntFunc(s: string): int
    requires |s| > 0
    requires (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
    ensures StringToIntFunc(s) >= 0
{
    var num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
        invariant num == (if i == 0 then 0 else StringToIntFunc(s[..i])) // This invariant might be tricky to maintain
    {
        num := num * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    num
}

function SplitIntsFunc(s: string): seq<int>
    requires (forall i :: 0 <= i < |s| ==> (IsDigit(s[i]) || s[i] == ' '))
    ensures (forall i :: 0 <= i < |SplitIntsFunc(s)| ==> SplitIntsFunc(s)[i] >= 0)
// This function parses a string containing space-separated non-negative integers.
// Example: "123 45 678" -> [123, 45, 678]
{
    var result: seq<int> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant (forall k :: 0 <= k < |result| ==> result[k] >= 0)
    {
        if s[i] == ' ' {
            i := i + 1;
        } else {
            var j := i;
            while j < |s| && IsDigit(s[j])
                invariant i <= j <= |s|
            {
                j := j + 1;
            }
            if j > i {
                result := result + [StringToIntFunc(s[i..j])];
            }
            i := j;
        }
    }
    result
}

predicate ValidIntLine(line: string) {
    |line| > 0 && (forall i :: 0 <= i < |line| ==> (IsDigit(line[i]) || line[i] == ' '))
}

predicate ValidIntLine(line: string, expectedCount: int) {
    ValidIntLine(line) && |SplitIntsFunc(line)| == expectedCount
}

function IntToStringFunc(n: int): string
    requires n >= 0
{
    if n == 0 then
        "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant (forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9')
            invariant (temp > 0 || (n == StringToIntFunc(s)))
        {
            s := (((temp % 10) as char) + '0') + s;
            temp := temp / 10;
        }
        s
}
function power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * power(base, exponent - 1)
}


function MinSeqFunc(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures var m := MinSeqFunc(s); m >= 1 && (exists i :: 0 <= i < |s| && s[i] == m) && (forall i :: 0 <= i < |s| ==> s[i] >= m)
{
    if |s| == 1 then
        s[0]
    else
        var m := s[0];
        var i := 1;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant m >= 1
            invariant (exists k :: 0 <= k < i && s[k] == m)
            invariant (forall k :: 0 <= k < i ==> s[k] >= m)
        {
            if s[i] < m then
                m := s[i];
            i := i + 1;
        }
        m
}

function MaxSeqFunc(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures var m := MaxSeqFunc(s); m >= 1 && (exists i :: 0 <= i < |s| && s[i] == m) && (forall i :: 0 <= i < |s| ==> s[i] <= m)
{
    if |s| == 1 then
        s[0]
    else
        var m := s[0];
        var i := 1;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant m >= 1
            invariant (exists k :: 0 <= k < i && s[k] == m)
            invariant (forall k :: 0 <= k < i ==> s[k] <= m)
        {
            if s[i] > m then
                m := s[i];
            i := i + 1;
        }
        m
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires '\n' in input
    requires ValidInput(input)
    ensures |result| > 0
    ensures exists n, m, r, S, B :: 
        ParseInput(input) == (n, m, r, S, B) &&
        n >= 1 && m >= 1 && r >= 1 &&
        |S| == n && |B| == m &&
        (forall i :: 0 <= i < |S| ==> S[i] >= 1) &&
        (forall i :: 0 <= i < |B| ==> B[i] >= 1) &&
        result == IntToStringFunc(ComputeMaxBourles(r, S, B)) + "\n"
// </vc-spec>
// <vc-code>
{
    var n, m, r, S, B := ParseInput(input);
    var maxBourles := ComputeMaxBourles(r, S, B);
    result := IntToStringFunc(maxBourles) + "\n";
}
// </vc-code>

