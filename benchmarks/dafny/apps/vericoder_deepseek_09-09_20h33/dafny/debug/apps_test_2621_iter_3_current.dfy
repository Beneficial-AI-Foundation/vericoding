predicate validInput(n: int, m: int, k: int, H: seq<int>)
{
    n >= 1 && n == |H| && m >= 0 && k >= 0 && 
    (forall i :: 0 <= i < |H| ==> H[i] >= 0)
}

function canReachEnd(n: int, m: int, k: int, H: seq<int>): bool
    requires validInput(n, m, k, H)
{
    simulateGame(0, m, n, k, H)
}

function simulateGame(pos: int, blocks: int, n: int, k: int, H: seq<int>): bool
    requires 0 <= pos < n
    requires n == |H|
    requires k >= 0
    requires blocks >= 0
    requires forall i :: 0 <= i < |H| ==> H[i] >= 0
    decreases n - pos
{
    if pos == n - 1 then
        true
    else
        var h1 := H[pos];
        var h2 := H[pos + 1];
        if h1 >= h2 then
            var newBlocks := if h2 >= k then blocks + (h1 - h2) + k else blocks + h1;
            simulateGame(pos + 1, newBlocks, n, k, H)
        else
            if h2 > h1 + blocks + k then
                false
            else
                var newBlocks := 
                    if h2 <= k then blocks + h1
                    else if (h2 - h1) <= k then blocks + k - (h2 - h1)
                    else blocks - (h2 - h1 - k);
                newBlocks >= 0 && simulateGame(pos + 1, newBlocks, n, k, H)
}

predicate validCompleteInputFormat(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate validOutputFormat(output: string, input: string)
{
    |output| >= 0 && 
    (output == "" || output[|output|-1] == '\n') &&
    (forall i :: 0 <= i < |output| ==> output[i] == 'Y' || output[i] == 'E' || output[i] == 'S' || output[i] == 'N' || output[i] == 'O' || output[i] == '\n')
}

predicate correctGameResults(output: string, input: string)
{
    true // Simplified for compilation
}

predicate outputMatchesTestCaseCount(output: string, input: string)
{
    true // Simplified for compilation
}

// <vc-helpers>
lemma simulateGameMaintainsInvariant(pos: int, blocks: int, n: int, k: int, H: seq<int>)
    requires 0 <= pos < n
    requires n == |H|
    requires k >= 0
    requires blocks >= 0
    requires forall i :: 0 <= i < |H| ==> H[i] >= 0
    decreases n - pos
    ensures if simulateGame(pos, blocks, n, k, H) then (blocks >= 0) else true
{
}

lemma newBlocksNonNegative(pos: int, blocks: int, n: int, k: int, H: seq<int>)
    requires 0 <= pos < n - 1
    requires blocks >= 0
    requires k >= 0
    requires forall i :: 0 <= i < |H| ==> H[i] >= 0
    requires H[pos] >= H[pos + 1]
    ensures var newBlocks := if H[pos + 1] >= k then blocks + (H[pos] - H[pos + 1]) + k else blocks + H[pos];
            newBlocks >= 0
{
}

lemma newBlocksElseCaseNonNegative(pos: int, blocks: int, n: int, k: int, H: seq<int>)
    requires 0 <= pos < n - 1
    requires blocks >= 0
    requires k >= 0
    requires forall i :: 0 <= i < |H| ==> H[i] >= 0
    requires H[pos] < H[pos + 1]
    requires H[pos + 1] <= H[pos] + blocks + k
{
    if H[pos + 1] <= k {
        // blocks + H[pos] >= 0 since both are >= 0
    } else if (H[pos + 1] - H[pos]) <= k {
        // blocks + k - (h2 - h1) >= 0 since k >= (h2 - h1) and blocks >= 0
    } else {
        // blocks - (h2 - h1 - k) >= 0 by the precondition h2 <= h1 + blocks + k
        // which implies h2 - h1 - k <= blocks, so blocks - (h2 - h1 - k) >= 0
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n'
    requires validCompleteInputFormat(stdin_input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] == 'Y' || result[i] == 'E' || result[i] == 'S' || result[i] == 'N' || result[i] == 'O' || result[i] == '\n'
    ensures result == "" || result[|result|-1] == '\n'
    ensures validOutputFormat(result, stdin_input)
    ensures correctGameResults(result, stdin_input)
    ensures outputMatchesTestCaseCount(result, stdin_input)
// </vc-spec>
// <vc-code>
{
    var nl := '\n';
    var lines := SplitLines(stdin_input);
    var t := ParseIntFromString(lines[0]);
    var index := 1;
    var output := "";
    
    var i := 0;
    while i < t
        decreases t - i
    {
        var parts := SplitStringIntoChars(lines[index]);
        index := index + 1;
        var n := ParseIntFromString(parts[0]);
        var m := ParseIntFromString(parts[1]);
        var k := ParseIntFromString(parts[2]);
        
        var H : seq<int> := [];
        var j := 0;
        while j < n
            decreases n - j
        {
            H := H + [ParseIntFromString(lines[index])];
            index := index + 1;
            j := j + 1;
        }
        
        if canReachEnd(n, m, k, H) {
            output := output + "YES" + nl;
        } else {
            output := output + "NO" + nl;
        }
        i := i + 1;
    }
    
    result := output;
}
// </vc-code>

