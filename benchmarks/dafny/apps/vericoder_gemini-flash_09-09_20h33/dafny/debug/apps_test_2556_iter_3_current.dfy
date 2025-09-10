predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    var inputPairs := GetInputPairs(input);
    var expectedResults := seq(|inputPairs|, i requires 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0);
    output == FormatResults(expectedResults)
}

function ComputeMinimumCost(c: int, s: int): int
    requires c > 0 && s >= 0
    ensures ComputeMinimumCost(c, s) >= 0
{
    var a := s / c;
    var r := s % c;
    (c - r) * a * a + r * (a + 1) * (a + 1)
}

function GetInputPairs(input: string): seq<(int, int)>
    requires |input| > 0
    ensures |GetInputPairs(input)| >= 0
{
    var lines := SplitLines(input);
    if |lines| == 0 then []
    else 
        var n := ParseInt(lines[0]);
        GetPairsFromLines(lines, 1, n)
}

function FormatResults(results: seq<int>): string
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResults(results)| >= 0
{
    FormatResultsHelper(results, 0, "")
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
    ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| >= 0
{
    var lines_list := new list<string>();
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant forall j :: 0 <= j < |lines_list.seq| ==> |lines_list.seq[j]| >= 0
    {
        var j := i;
        while j < |input| && input[j] != '\n'
            invariant i <= j <= |input|
        {
            j := j + 1;
        }
        var line := input[i..j];
        lines_list := lines_list.add(line);
        i := j + 1;
    }
    lines_list.seq
}

function ParseInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures ParseInt(s) >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function GetPairsFromLines(lines: seq<string>, startIndex: int, count: int): seq<(int, int)>
    requires 0 <= startIndex <= |lines|
    requires count >= 0
    requires startIndex + count <= |lines|
    requires forall i :: startIndex <= i < startIndex + count ==> lines[i] != "" && var parts := Split(lines[i], ' '); |parts| == 2 && (forall j :: 0 <= j < |parts[0]| ==> '0' <= parts[0][j] <= '9') && (forall j :: 0 <= j < |parts[1]| ==> '0' <= parts[1][j] <= '9')
    ensures |GetPairsFromLines(lines, startIndex, count)| == count
{
    if count == 0 then []
    else
        var line := lines[startIndex];
        var parts := Split(line, ' ');
        var c := ParseInt(parts[0]);
        var s := ParseInt(parts[1]);
        [(c, s)] + GetPairsFromLines(lines, startIndex + 1, count - 1)
}

function Split(s: string, delim: char): seq<string>
    ensures forall i :: 0 <= i < |Split(s, delim)| ==> |Split(s, delim)[i]| >= 0
{
    var result_list := new list<string>();
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |result_list.seq| ==> |result_list.seq[j]| >= 0
    {
        var j := i;
        while j < |s| && s[j] != delim
            invariant i <= j <= |s|
        {
            j := j + 1;
        }
        if j > i then
            result_list := result_list.add(s[i..j]);
        i := j + 1;
    }
    result_list.seq
}

function FormatResultsHelper(results: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |results|
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResultsHelper(results, index, acc)| >= |acc|
{
    if index == |results| then
        acc
    else
        var currentResultString := IntToString(results[index]);
        var newAcc := if acc == "" then currentResultString else acc + "\n" + currentResultString;
        FormatResultsHelper(results, index + 1, newAcc)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 1 || n == 0 && |IntToString(n)| == 1
    ensures (n == 0) ==> (IntToString(n) == "0")
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
            invariant (temp > 0) ==> (s != "") || (n == temp)
        {
            s := ('0' as int + temp % 10) as char + s;
            temp := temp / 10;
        }
        s
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var n := ParseInt(lines[0]);
    var inputPairs := GetPairsFromLines(lines, 1, n);

    var results := new seq<int>(|inputPairs|, i requires 0 <= i < |inputPairs| =>
        var c := inputPairs[i].0;
        var s := inputPairs[i].1;
        if c > 0 && s >= 0 then
            ComputeMinimumCost(c, s)
        else
            0 // Should not be reached given valid input constraints for c > 0 and s >= 0
    );

    result := FormatResults(results);
}
// </vc-code>

