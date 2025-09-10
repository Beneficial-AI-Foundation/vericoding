predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i !in arthurSet ==> result[2*(i-1)] == '2')
}

// <vc-helpers>
function SplitLines(s: string) : seq<string>
{
    s.Split('\n')
}

function SplitSpaces(s: string) : seq<string>
{
    s.Split(' ')
}

function ParseInt(s: string) : int
    requires forall c :: c in s ==> '0' <= c <= '9'
    requires |s| > 0
{
    StringToInt(s)
}

function ParseIntSeq(s: seq<string>) : seq<int>
    requires forall i :: 0 <= i < |s| ==> (forall c :: c in s[i] ==> '0' <= c <= '9') && |s[i]| > 0
{
    if |s| == 0 then []
    else [ParseInt(s[0])] + ParseIntSeq(s[1..])
}

function StringToInt(s: string) : int
    requires forall c :: c in s ==> '0' <= c <= '9'
    requires |s| > 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == StringToPartialInt(s[..i])
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function StringToPartialInt(s: seq<char>) : int
    requires forall c :: c in s ==> '0' <= c <= '9'
{
    if |s| == 0 then 0
    else
        (var res := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant res == StringToPartialInt(s[..i])
        {
            res := res * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        res)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<char>)
    requires |input| > 0
    ensures !ValidInput(input) ==> |result| == 0
    ensures ValidInput(input) ==> ValidOutput(input, result) && CorrectAssignment(input, result)
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == ' '
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return [];
    }

    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet: set<int> := set x | x in arthurApples;

    var result_seq: seq<char> := [];

    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant |result_seq| == 2*i || (i == 0 && |result_seq| == 0) // Adjusted invariant
        invariant forall j :: 0 <= j < i ==> result_seq[2*j] == '1' || result_seq[2*j] == '2'
        invariant forall j :: 0 <= j < i-1 ==> result_seq[2*j+1] == ' '
        invariant forall j :: 1 <= j <= i ==> (j in arthurSet ==> result_seq[2*(j-1)] == '1') && (j !in arthurSet ==> result_seq[2*(j-1)] == '2')
    {
        var char_to_add: char;
        if (i+1) in arthurSet {
            char_to_add := '1';
        } else {
            char_to_add := '2';
        }
        result_seq := result_seq + [char_to_add];
        if i < n - 1 {
            result_seq := result_seq + [' '];
        }
    }

    return result_seq;
}
// </vc-code>

