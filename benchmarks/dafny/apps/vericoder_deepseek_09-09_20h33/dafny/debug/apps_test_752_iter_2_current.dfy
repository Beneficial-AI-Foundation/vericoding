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
function countSizes(lines: seq<string>): seq<nat>
    requires |lines| > 0
    ensures |countSizes(lines)| == |lines|
    ensures forall i :: 0 <= i < |lines| ==> countSizes(lines)[i] == |lines[i]|
{
    if |lines| == 0 then []
    else [|lines[0]|] + countSizes(lines[1..])
}

function countUnmatchedSizes(prevSizes: seq<nat>, currentSizes: seq<string>): nat
    requires |prevSizes| == |currentSizes|
    ensures countUnmatchedSizes(prevSizes, currentSizes) <= |prevSizes|
{
    if |prevSizes| == 0 then 0
    else
        var currentSize := |currentSizes[0]|;
        var rest := countUnmatchedSizes(prevSizes[1..], currentSizes[1..]);
        if prevSizes[0] != currentSize then rest + 1 else rest
}

lemma CountSizesLemma(lines: seq<string>)
    requires |lines| > 0
    ensures countSizes(lines) == seq(|lines|, i requires 0 <= i < |lines| => |lines[i]|)
{}

lemma CountUnmatchedSizesLemma(prevSizes: seq<nat>, currentSizes: seq<string>)
    requires |prevSizes| == |currentSizes|
    ensures countUnmatchedSizes(prevSizes, currentSizes) ==
        |seq k | 0 <= k < |prevSizes| && prevSizes[k] != |currentSizes[k]| |
{}
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
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    
    if n == 0 {
        result := "0\n";
        return;
    }
    
    var mismatches := 0;
    var i: int := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant mismatches == |seq j | 0 <= j < i && |lines[j+1]| != |lines[n+1+j]| |
    {
        var prevSize := |lines[i+1]|;
        var currentSize := |lines[n+1+i]|;
        
        if prevSize != currentSize {
            mismatches := mismatches + 1;
        }
        
        i := i + 1;
    }
    
    result := intToString(mismatches) + "\n";
}
// </vc-code>

