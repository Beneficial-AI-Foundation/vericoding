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
lemma SplitLinesNonEmpty(s: string)
    ensures |SplitLines(s)| > 0
{
}

lemma ParseIntValid(s: string)
    requires |s| > 0
    ensures ParseInt(s) >= 0
{
}

lemma ParseIntSeqValid(s: seq<string>)
    ensures forall x :: x in ParseIntSeq(s) ==> x >= 0
{
}

lemma ArthurApplesValid(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
            var n := ParseInt(SplitSpaces(lines[0])[0]);
            var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
            |arthurApples| == n && forall x :: x in arthurApples ==> 1 <= x <= n
{
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
        result := [];
    } else {
        var lines := SplitLines(input);
        var n := ParseInt(SplitSpaces(lines[0])[0]);
        var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
        var arthurSet := set x | x in arthurApples;
        
        var i := 0;
        result := [];
        while i < n
            invariant |result| == 2*i
            invariant forall j :: 0 <= j < i ==> (result[2*j] == '1' || result[2*j] == '2')
            invariant forall j :: 0 <= j < i-1 ==> result[2*j+1] == ' '
            invariant forall k :: 0 <= k < |result| ==> result[k] == '1' || result[k] == '2' || result[k] == ' '
        {
            if i > 0 {
                result := result + [' '];
            }
            if (i+1) in arthurSet {
                result := result + ['1'];
            } else {
                result := result + ['2'];
            }
            i := i + 1;
        }
    }
}
// </vc-code>

