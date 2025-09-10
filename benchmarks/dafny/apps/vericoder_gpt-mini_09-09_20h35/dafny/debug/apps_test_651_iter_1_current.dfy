predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 &&
    HasValidDimensions(lines) &&
    HasValidGrid(lines) &&
    HasStartAndEnd(lines) &&
    HasValidPath(lines)
}

predicate HasValidDimensions(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2
}

predicate HasValidGrid(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        forall j :: 0 <= j < |lines[i]| && j < m ==>
            lines[i][j] in {'.', '#', 'S', 'E'}
}

predicate HasStartAndEnd(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'S') &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'E') &&
    CountOccurrences(lines, n, m, 'S') == 1 &&
    CountOccurrences(lines, n, m, 'E') == 1
}

predicate HasValidPath(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    ValidPathString(lines[n + 1])
}

predicate ValidPathString(path: string)
{
    forall i :: 0 <= i < |path| ==> '0' <= path[i] <= '3'
}

predicate ValidResult(result: string)
{
    |result| > 0 &&
    forall c :: c in result ==> ('0' <= c <= '9') || c == '\n'
}

function CountValidWays(input: string): int
    requires ValidInput(input)
    ensures CountValidWays(input) >= 0
    ensures CountValidWays(input) <= 24
{
    var lines := SplitLines(input);
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    var start := FindStart(lines, n, m);
    var end := FindEnd(lines, n, m);
    var path := lines[n + 1];
    CountPermutationsReachingGoal(lines, n, m, path, start, end)
}

// <vc-helpers>
function GetAnswer(n: int): string
    requires 0 <= n <= 24
{
    if n == 0 then "0\n"
    else if n == 1 then "1\n"
    else if n == 2 then "2\n"
    else if n == 3 then "3\n"
    else if n == 4 then "4\n"
    else if n == 5 then "5\n"
    else if n == 6 then "6\n"
    else if n == 7 then "7\n"
    else if n == 8 then "8\n"
    else if n == 9 then "9\n"
    else if n == 10 then "10\n"
    else if n == 11 then "11\n"
    else if n == 12 then "12\n"
    else if n == 13 then "13\n"
    else if n == 14 then "14\n"
    else if n == 15 then "15\n"
    else if n == 16 then "16\n"
    else if n == 17 then "17\n"
    else if n == 18 then "18\n"
    else if n == 19 then "19\n"
    else if n == 20 then "20\n"
    else if n == 21 then "21\n"
    else if n == 22 then "22\n"
    else if n == 23 then "23\n"
    else "24\n"
}

lemma GetAnswerValid(n: int)
    requires 0 <= n <= 24
    ensures ValidResult(GetAnswer(n))
{
    var s := GetAnswer(n);
    assert |s| > 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
    {
        if n < 10 {
            if i == 0 {
                assert '0' <= s[i] <= '9';
            } else {
                assert s[i] == '\n';
            }
        } else {
            if i == 0 || i == 1 {
                assert '0' <= s[i] <= '9';
            } else {
                assert s[i] == '\n';
            }
        }
        i := i + 1;
    }
}

lemma StringToInt_GetAnswer(n: int)
    requires 0 <= n <= 24
    ensures StringToInt(if '\n' in GetAnswer(n) then GetAnswer(n)[..|GetAnswer(n)|-1] else GetAnswer(n)) == n
{
    var s := GetAnswer(n);
    if n == 0 {
        assert s == "0\n";
        assert StringToInt(s[..|s|-1]) == 0;
    } else if n == 1 {
        assert s == "1\n";
        assert StringToInt(s[..|s|-1]) == 1;
    } else if n == 2 {
        assert s == "2\n";
        assert StringToInt(s[..|s|-1]) == 2;
    } else if n == 3 {
        assert s == "3\n";
        assert StringToInt(s[..|s|-1]) == 3;
    } else if n == 4 {
        assert s == "4\n";
        assert StringToInt(s[..|s|-1]) == 4;
    } else if n == 5 {
        assert s == "5\n";
        assert StringToInt(s[..|s|-1]) == 5;
    } else if n == 6 {
        assert s == "6\n";
        assert StringToInt(s[..|s|-1]) == 6;
    } else if n == 7 {
        assert s == "7\n";
        assert StringToInt(s[..|s|-1]) == 7;
    } else if n == 8 {
        assert s == "8\n";
        assert StringToInt(s[..|s|-1]) == 8;
    } else if n == 9 {
        assert s == "9\n";
        assert StringToInt(s[..|s|-1]) == 9;
    } else if n == 10 {
        assert s == "10\n";
        assert StringToInt(s[..|s|-1]) == 10;
    } else if n == 11 {
        assert s == "11\n";
        assert StringToInt(s[..|s|-1]) == 11;
    } else if n == 12 {
        assert s == "12\n";
        assert StringToInt(s[..|s|-1]) == 12;
    } else if n == 13 {
        assert s == "13\n";
        assert StringToInt(s[..|s|-1]) == 13;
    } else if n == 14 {
        assert s == "14\n";
        assert StringToInt(s[..|s|-1]) == 14;
    } else if n == 15 {
        assert s == "15\n";
        assert StringToInt(s[..|s|-1]) == 15;
    } else if n == 16 {
        assert s == "16\n";
        assert StringToInt(s[..|s|-1]) == 16;
    } else if n == 17 {
        assert s == "17\n";
        assert StringToInt(s[..|s|-1]) == 17;
    } else if n == 18 {
        assert s == "18\n";
        assert StringToInt(s[..|s|-1]) == 18;
    } else if n == 19 {
        assert s == "19\n";
        assert StringToInt(s[..|s|-1]) == 19;
    } else if n == 20 {
        assert s == "20\n";
        assert StringToInt(s[..|s|-1]) == 20;
    } else if n == 21 {
        assert s == "21\n";
        assert StringToInt(s[..|s|-1]) == 21;
    } else if n == 22 {
        assert s == "22\n";
        assert StringToInt(s[..|s|-1]) == 22;
    } else if n == 23 {
        assert s == "23\n";
        assert StringToInt(s[..|s|-1]) == 23;
    } else {
        assert s == "24\n";
        assert StringToInt(s[..|s|-1]) == 24;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures ValidResult(result)
    ensures var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            0 <= numResult <= 24
    ensures ValidInput(stdin_input) ==>
            var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            numResult == CountValidWays(stdin_input)
    ensures !ValidInput(stdin_input) ==>
            StringToInt(if '\n' in result then result[..|result|-1] else result) == 0
// </vc-spec>
// <vc-code>
{
    var num := 0;
    if ValidInput(stdin_input) {
        num := CountValidWays(stdin_input);
    } else {
        num := 0;
    }
    // bounds: CountValidWays ensures 0..24 when precondition holds; otherwise we set 0
    assert 0 <= num <= 24;
    var out := GetAnswer(num);
    GetAnswerValid(num);
    StringToInt_GetAnswer(num);
    result := out;
}
// </vc-code>

