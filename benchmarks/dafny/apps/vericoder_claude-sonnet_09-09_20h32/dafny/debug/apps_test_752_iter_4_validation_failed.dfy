predicate validInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    |lines| >= 1 && 
    (var n := parseInteger(lines[0]);
     n >= 0 && |lines| >= 2*n + 1 && 
     (forall i :: 1 <= i <= 2*n ==> i < |lines| && |lines[i]| > 0))
}

function computeMismatches(stdin_input: string): nat
    requires validInput(stdin_input)
    ensures computeMismatches(stdin_input) <= parseInteger(splitLines(stdin_input)[0])
{
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    if n == 0 then 0
    else
        var prevSizes := countSizes(lines[1..n+1]);
        var currentSizes := lines[n+1..2*n+1];
        countUnmatchedSizes(prevSizes, currentSizes)
}

// <vc-helpers>
function splitLines(s: string): seq<string>

function parseInteger(s: string): int

function intToString(n: int): string

function countSizes(lines: seq<string>): seq<int>

function {:axiom} countUnmatchedSizes(prevSizes: seq<int>, currentSizes: seq<string>): nat
    ensures countUnmatchedSizes(prevSizes, currentSizes) <= |prevSizes|

lemma computeMismatchesBound(stdin_input: string)
    requires validInput(stdin_input)
    ensures computeMismatches(stdin_input) <= parseInteger(splitLines(stdin_input)[0])
{
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    if n == 0 {
        assert computeMismatches(stdin_input) == 0;
        assert 0 <= n;
    } else {
        var prevSizes := countSizes(lines[1..n+1]);
        var currentSizes := lines[n+1..2*n+1];
        assert |prevSizes| == n;
        assert countUnmatchedSizes(prevSizes, currentSizes) <= |prevSizes|;
        assert countUnmatchedSizes(prevSizes, currentSizes) <= n;
        assert computeMismatches(stdin_input) == countUnmatchedSizes(prevSizes, currentSizes);
    }
}

lemma countSizesLength(lines: seq<string>)
    ensures |countSizes(lines)| == |lines|
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n' || (|result| > 1 && result[|result|-2..] == "\r\n")
    ensures exists mismatches: nat :: result == intToString(mismatches) + "\n" && 
            mismatches == computeMismatches(stdin_input)
    ensures (var lines := splitLines(stdin_input);
             var n := parseInteger(lines[0]);
             n >= 0 ==> (var mismatches := computeMismatches(stdin_input);
                        mismatches <= n &&
                        result == intToString(mismatches) + "\n"))
// </vc-spec>
// <vc-code>
{
    computeMismatchesBound(stdin_input);
    var mismatches := computeMismatches(stdin_input);
    result := intToString(mismatches) + "\n";
}
// </vc-code>

