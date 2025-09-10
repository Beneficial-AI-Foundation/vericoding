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
function SplitLines(s: string): seq<string>

function SplitSpaces(s: string): seq<string>

function ParseInt(s: string): int

function ParseIntSeq(tokens: seq<string>): seq<int>
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
    if |input| == 0 {
        return [];
    }
    
    var lines := SplitLines(input);
    if |lines| < 3 {
        return [];
    }
    
    var firstLineTokens := SplitSpaces(lines[0]);
    if |firstLineTokens| < 3 {
        return [];
    }
    
    var n := ParseInt(firstLineTokens[0]);
    if n <= 0 {
        return [];
    }
    
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    
    result := [];
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |result| == 2 * (i - 1) - (if i == 1 then 0 else 1)
        invariant forall j :: 0 <= j < |result| ==> result[j] == '1' || result[j] == '2' || result[j] == ' '
        invariant forall j :: 1 <= j < i ==> 
            (j in arthurSet ==> result[2*(j-1)] == '1') &&
            (j !in arthurSet ==> result[2*(j-1)] == '2')
        invariant forall j :: 0 <= j < i-1 ==> result[2*j+1] == ' '
    {
        if i > 1 {
            result := result + [' '];
        }
        
        if i in arthurSet {
            result := result + ['1'];
        } else {
            result := result + ['2'];
        }
        
        i := i + 1;
    }
}
// </vc-code>

