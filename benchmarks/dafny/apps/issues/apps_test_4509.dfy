// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    var lines := SplitByNewline(input);
    |lines| > 0 &&
    var t := ParseInt(lines[0]);
    t > 0 && t <= 1000 &&
    |lines| >= t + 1 &&
    forall i :: 1 <= i <= t ==> 
        var parts := SplitBySpace(lines[i]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var k := ParseInt(parts[1]);
        2 <= n <= 1000000000 && 1 <= k <= 1000000000
}

function CountNonDivisible(x: int, n: int): int
    requires x >= 0
    requires n > 0
{
    x - x / n
}

function KthNonDivisible(n: int, k: int): int
    requires n >= 2
    requires k >= 1
    ensures KthNonDivisible(n, k) >= -1
    ensures KthNonDivisible(n, k) != -1 ==> CountNonDivisible(KthNonDivisible(n, k), n) >= k
    ensures KthNonDivisible(n, k) > 0 ==> forall x :: 1 <= x < KthNonDivisible(n, k) ==> CountNonDivisible(x, n) < k
{
    var lo := 1;
    var hi := 10000000000000000000;
    FindKthNonDivisible(n, k, lo, hi)
}

function GetTestCaseCount(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewline(input);
    ParseInt(lines[0])
}

function GetTestCase(input: string, index: int): (int, int)
    requires ValidInput(input)
    requires 0 <= index < GetTestCaseCount(input)
{
    var lines := SplitByNewline(input);
    var parts := SplitBySpace(lines[index + 1]);
    (ParseInt(parts[0]), ParseInt(parts[1]))
}

function ComputeAllAnswers(input: string): seq<int>
    requires ValidInput(input)
    ensures |ComputeAllAnswers(input)| == GetTestCaseCount(input)
    ensures forall i :: 0 <= i < |ComputeAllAnswers(input)| ==> 
        var testCase := GetTestCase(input, i);
        ComputeAllAnswers(input)[i] == KthNonDivisible(testCase.0, testCase.1)
{
    var lines := SplitByNewline(input);
    var t := ParseInt(lines[0]);
    ComputeAnswersHelper(input, 0, t)
}

predicate ResultMatchesPythonOutput(input: string, output: string)
    requires ValidInput(input)
{
    var expectedAnswers := ComputeAllAnswers(input);
    output == FormatAnswers(expectedAnswers)
}
// </vc-preamble>

// <vc-helpers>
function FindKthNonDivisible(n: int, k: int, lo: int, hi: int): int
    requires n >= 2
    requires k >= 1
    requires lo >= 1
    requires hi >= lo - 1
    ensures FindKthNonDivisible(n, k, lo, hi) >= -1
    decreases hi - lo + 1
{
    if lo > hi then -1
    else
        var mid := (lo + hi) / 2;
        var count := CountNonDivisible(mid, n);
        if count >= k && (mid == 1 || CountNonDivisible(mid - 1, n) < k) then mid
        else if count < k then FindKthNonDivisible(n, k, mid + 1, hi)
        else FindKthNonDivisible(n, k, lo, mid - 1)
}

function ComputeAnswersHelper(input: string, index: int, total: int): seq<int>
    requires ValidInput(input)
    requires 0 <= index <= total <= GetTestCaseCount(input)
    ensures |ComputeAnswersHelper(input, index, total)| == total - index
    decreases total - index
{
    if index >= total then []
    else 
        var testCase := GetTestCase(input, index);
        var answer := KthNonDivisible(testCase.0, testCase.1);
        [answer] + ComputeAnswersHelper(input, index + 1, total)
}

function FormatAnswers(answers: seq<int>): string
{
    if |answers| == 0 then ""
    else if |answers| == 1 then IntToString(answers[0]) + "\n"
    else IntToString(answers[0]) + "\n" + FormatAnswers(answers[1..])
}

function IntToString(n: int): string
{
    if n < 0 then "-1"
    else if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else 
        var digit := (n % 10) as char + ('0' as int) as char;
        IntToStringHelper(n / 10, [digit] + acc)
}

function SplitByNewline(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, '\n');
        if pos == -1 then [s]
        else if pos < |s| then [s[..pos]] + SplitByNewline(s[pos+1..])
        else [s]
}

function SplitBySpace(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, ' ');
        if pos == -1 then [s]
        else if pos < |s| then [s[..pos]] + SplitBySpace(s[pos+1..])
        else [s]
}

function FindChar(s: string, c: char): int
    ensures FindChar(s, c) == -1 || (0 <= FindChar(s, c) < |s|)
{
    FindCharHelper(s, c, 0)
}

function FindCharHelper(s: string, c: char, index: int): int
    requires 0 <= index
    ensures FindCharHelper(s, c, index) == -1 || (index <= FindCharHelper(s, c, index) < |s|)
    decreases |s| - index
{
    if index >= |s| then -1
    else if s[index] == c then index
    else FindCharHelper(s, c, index + 1)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index
    decreases |s| - index
{
    if index >= |s| then acc
    else
        var digit := s[index] as int - '0' as int;
        ParseIntHelper(s, index + 1, acc * 10 + digit)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ResultMatchesPythonOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    var t := ParseInt(lines[0]);
    var answers := [];

    for i := 1 to t
        invariant |answers| == i - 1
        invariant forall j :: 0 <= j < |answers| ==> answers[j] >= -1
        invariant forall j :: 0 <= j < |answers| ==> 
            var testCase := GetTestCase(input, j);
            var n := testCase.0;
            var k := testCase.1;
            answers[j] == KthNonDivisible(n, k)
    {
        var parts := SplitBySpace(lines[i]);
        var n := ParseInt(parts[0]);
        var k := ParseInt(parts[1]);

        var lo := 1;
        var hi := 10000000000000000000;
        var ans := -1;

        while lo <= hi
            decreases hi - lo
            invariant lo >= 1
            invariant hi >= lo - 1
            invariant ans == -1 ==> forall x :: 1 <= x < lo ==> CountNonDivisible(x, n) < k
            invariant ans != -1 ==> ans >= 1 && CountNonDivisible(ans, n) >= k
            invariant ans != -1 ==> ans >= lo - 1
            invariant ans != -1 ==> forall x :: 1 <= x < ans ==> CountNonDivisible(x, n) < k
        {
            var mid := (lo + hi) / 2;
            var divi := mid - mid / n;

            if divi >= k {
                ans := mid;
                hi := mid - 1;
            } else {
                lo := mid + 1;
            }
        }

        answers := answers + [ans];
    }

    result := FormatAnswers(answers);
}
// </vc-code>
