// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitLinesLogical(input);
    |lines| >= 1 && 
    (forall line :: line in lines ==> |line| > 0) &&
    1 <= ParseIntLogical(lines[0]) <= 200 &&
    |lines| >= 1 + 2 * ParseIntLogical(lines[0]) &&
    (forall tc :: 0 <= tc < ParseIntLogical(lines[0]) ==>
        var nkLine := SplitWhitespaceLogical(lines[1 + tc * 2]);
        |nkLine| >= 2 &&
        var n := ParseIntLogical(nkLine[0]);
        var k := ParseIntLogical(nkLine[1]);
        1 <= n <= 200 && 1 <= k <= n &&
        var tapLine := SplitWhitespaceLogical(lines[1 + tc * 2 + 1]);
        |tapLine| == k &&
        (forall i :: 0 <= i < k ==> 1 <= ParseIntLogical(tapLine[i]) <= n) &&
        (forall i :: 0 <= i < k - 1 ==> ParseIntLogical(tapLine[i]) < ParseIntLogical(tapLine[i + 1])))
}

predicate ValidOutput(output: string, input: string)
{
    var inputLines := SplitLinesLogical(input);
    var outputLines := SplitLinesLogical(output);
    |inputLines| >= 1 ==>
    var t := ParseIntLogical(inputLines[0]);
    |outputLines| == t &&
    (forall line :: line in outputLines ==> |line| > 0) &&
    (forall line :: line in outputLines ==> 
        (forall c :: c in line ==> c >= '0' && c <= '9') &&
        ParseIntLogical(line) >= 1)
}

predicate CorrectSolution(input: string, output: string)
{
    var inputLines := SplitLinesLogical(input);
    var outputLines := SplitLinesLogical(output);
    |inputLines| >= 1 ==>
    var t := ParseIntLogical(inputLines[0]);
    |outputLines| == t &&
    forall tc :: 0 <= tc < t ==>
        var nkLine := SplitWhitespaceLogical(inputLines[1 + tc * 2]);
        var n := ParseIntLogical(nkLine[0]);
        var k := ParseIntLogical(nkLine[1]);
        var tapLine := SplitWhitespaceLogical(inputLines[1 + tc * 2 + 1]);
        var taps := seq(k, i => ParseIntLogical(tapLine[i]));
        var result := ParseIntLogical(outputLines[tc]);
        result == MaxMinTimeToWater(n, taps)
}

function MaxMinTimeToWater(n: int, taps: seq<int>): (result: int)
  requires n > 0 && |taps| > 0
  requires forall i :: 0 <= i < |taps| ==> 1 <= taps[i] <= n
  ensures result >= 1
{
    var minTimes := seq(n, bedPos requires 0 <= bedPos < n => MinTimeToReachBed(bedPos + 1, taps));
    SeqMax(minTimes)
}

function MinTimeToReachBed(bedPos: int, taps: seq<int>): (result: int)
  requires bedPos >= 1 && |taps| > 0
  ensures result >= 1
{
    var distances := seq(|taps|, i requires 0 <= i < |taps| => Abs(taps[i] - bedPos) + 1);
    SeqMin(distances)
}

function SeqMax(s: seq<int>): (result: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures result >= 1
{
    if |s| == 1 then s[0]
    else
        var rest := SeqMax(s[1..]);
        if s[0] > rest then s[0] else rest
}

function SeqMin(s: seq<int>): (result: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures result >= 1
{
    if |s| == 1 then s[0]
    else
        var rest := SeqMin(s[1..]);
        if s[0] < rest then s[0] else rest
}

function SplitLinesLogical(s: string): seq<string>
{
    var result := [];
    result
}

function SplitWhitespaceLogical(s: string): seq<string>
{
    var result := [];
    result
}

function ParseIntLogical(s: string): int
  requires |s| > 0
{
    0
}

function Abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
method IntToString(x: int) returns (s: string)
  ensures |s| > 0
  ensures (x >= 0) ==> (forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9')
  ensures (x < 0) ==> (s[0] == '-' && forall i :: 1 <= i < |s| ==> s[i] >= '0' && s[i] <= '9')
{
    if x == 0 {
        s := "0";
        return;
    }

    var negative := x < 0;
    var val := if negative then -x else x;
    s := "";

    assert val > 0;

    while val > 0
        invariant val >= 0
        invariant forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
        invariant val == 0 ==> |s| > 0
    {
        var digit := val % 10;
        var digitChar := (digit + '0' as int) as char;
        s := [digitChar] + s;
        val := val / 10;
    }

    if negative {
        s := "-" + s;
    }
}

method SplitLines(s: string) returns (lines: seq<string>)
  requires |s| > 0
  ensures |lines| > 0
{
    lines := [];
    var current := "";
    var i := 0;
    while i < |s|
    {
        if s[i] == '\n' {
            if |current| > 0 {
                lines := lines + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        lines := lines + [current];
    }

    if |lines| == 0 {
        lines := [s];
    }
}

method SplitWhitespace(s: string) returns (parts: seq<string>)
  requires |s| > 0
  ensures |parts| > 0
{
    parts := [];
    var current := "";
    var i := 0;
    while i < |s|
    {
        if s[i] == ' ' || s[i] == '\t' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        parts := parts + [current];
    }

    if |parts| == 0 {
        parts := [s];
    }
}

method ParseInt(s: string) returns (value: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> (s[i] >= '0' && s[i] <= '9') || (i == 0 && s[i] == '-')
{
    value := 0;
    var i := 0;
    var sign := 1;
    if |s| > 0 && s[0] == '-' {
        sign := -1;
        i := 1;
    }
    while i < |s|
    {
        var digit := s[i] as int - '0' as int;
        value := value * 10 + digit;
        i := i + 1;
    }
    value := value * sign;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  requires ValidInput(input)
  ensures |result| > 0
  ensures ValidOutput(result, input)
  ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var lineIndex := 0;
    var t := ParseInt(lines[lineIndex]);
    lineIndex := lineIndex + 1;

    var output := "";
    var testCase := 0;

    while testCase < t
    {
        var nkLine := SplitWhitespace(lines[lineIndex]);
        var n := ParseInt(nkLine[0]);
        var k := ParseInt(nkLine[1]);
        lineIndex := lineIndex + 1;

        var tapLine := SplitWhitespace(lines[lineIndex]);
        var taps := new int[k];
        var tapIndex := 0;
        while tapIndex < k
        {
            taps[tapIndex] := ParseInt(tapLine[tapIndex]);
            tapIndex := tapIndex + 1;
        }
        lineIndex := lineIndex + 1;

        var maxTime := 0;
        var bedPos := 1;
        while bedPos <= n
        {
            var minDist := 1000000;
            var tapIdx := 0;
            while tapIdx < k
            {
                var tmpCall1 := Abs(taps[tapIdx] - bedPos);
                var dist := tmpCall1 + 1;
                if dist < minDist {
                    minDist := dist;
                }
                tapIdx := tapIdx + 1;
            }
            if minDist > maxTime {
                maxTime := minDist;
            }
            bedPos := bedPos + 1;
        }

        var tmpCall2 := IntToString(maxTime);
        output := output + tmpCall2;
        if testCase < t - 1 {
            output := output + "\n";
        }
        testCase := testCase + 1;
    }

    result := output;
}
// </vc-code>
