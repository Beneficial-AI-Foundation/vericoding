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
function parseInt(s: string, start: int, end: int): (int, bool)
    requires 0 <= start <= end <= |s|
    ensures var (r, s) := parseInt(s, start, end); !s ==> r == 0
{
    if start >= end then (0, false)
    else if end - start > 10 then (0, false)  // Prevent overflow
    else
        var isNeg := s[start] == '-';
        var realStart := if isNeg then start + 1 else start;
        if realStart >= end then (0, false)
        else parseNat(s, realStart, end, isNeg)
}

function parseNat(s: string, start: int, end: int, isNeg: bool): (int, bool)
    requires 0 <= start <= end <= |s|
    ensures var (r, s) := parseNat(s, start, end, isNeg); !s ==> r == 0
{
    if start >= end then (0, false)
    else if forall i :: start <= i < end ==> '0' <= s[i] <= '9' then
        var val := parseNatHelper(s, start, end, 0);
        if isNeg then (-val, true) else (val, true)
    else (0, false)
}

function parseNatHelper(s: string, start: int, end: int, acc: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    decreases end - start
{
    if start >= end then acc
    else parseNatHelper(s, start + 1, end, acc * 10 + (s[start] - '0') as int)
}

function skipWhitespace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= skipWhitespace(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then start
    else if s[start] == ' ' || s[start] == '\t' || s[start] == '\n' || s[start] == '\r' then
        skipWhitespace(s, start + 1)
    else start
}

function findNextWhitespace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= findNextWhitespace(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then start
    else if s[start] == ' ' || s[start] == '\t' || s[start] == '\n' || s[start] == '\r' then start
    else findNextWhitespace(s, start + 1)
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
    result := "";
    var pos := 0;
    
    // Parse number of test cases
    pos := skipWhitespace(stdin_input, pos);
    var nextPos := findNextWhitespace(stdin_input, pos);
    var (t, success) := parseInt(stdin_input, pos, nextPos);
    if !success || t < 0 {
        result := "NO\n";  // Ensure result ends with \n
        return;
    }
    pos := nextPos;
    
    var testCase := 0;
    while testCase < t
        invariant 0 <= testCase <= t
        invariant 0 <= pos <= |stdin_input|
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> result[i] == 'Y' || result[i] == 'E' || result[i] == 'S' || result[i] == 'N' || result[i] == 'O' || result[i] == '\n'
    {
        // Parse n, m, k
        pos := skipWhitespace(stdin_input, pos);
        nextPos := findNextWhitespace(stdin_input, pos);
        var (n, success1) := parseInt(stdin_input, pos, nextPos);
        if !success1 || n < 1 {
            result := result + "NO\n";
            testCase := testCase + 1;
            continue;
        }
        pos := nextPos;
        
        pos := skipWhitespace(stdin_input, pos);
        nextPos := findNextWhitespace(stdin_input, pos);
        var (m, success2) := parseInt(stdin_input, pos, nextPos);
        if !success2 || m < 0 {
            result := result + "NO\n";
            testCase := testCase + 1;
            continue;
        }
        pos := nextPos;
        
        pos := skipWhitespace(stdin_input, pos);
        nextPos := findNextWhitespace(stdin_input, pos);
        var (k, success3) := parseInt(stdin_input, pos, nextPos);
        if !success3 || k < 0 {
            result := result + "NO\n";
            testCase := testCase + 1;
            continue;
        }
        pos := nextPos;
        
        // Parse H array
        var H := [];
        var i := 0;
        var skipRest := false;
        while i < n
            invariant 0 <= i <= n
            invariant |H| == i || skipRest
            invariant forall j :: 0 <= j < |H| ==> H[j] >= 0
            invariant 0 <= pos <= |stdin_input|
        {
            if skipRest {
                i := i + 1;
                continue;
            }
            pos := skipWhitespace(stdin_input, pos);
            nextPos := findNextWhitespace(stdin_input, pos);
            var (h, success4) := parseInt(stdin_input, pos, nextPos);
            if !success4 || h < 0 {
                result := result + "NO\n";
                skipRest := true;
                i := i + 1;
                continue;
            }
            H := H + [h];
            pos := nextPos;
            i := i + 1;
        }
        
        if !skipRest && |H| == n {
            if validInput(n, m, k, H) {
                if canReachEnd(n, m, k, H) {
                    result := result + "YES\n";
                } else {
                    result := result + "NO\n";
                }
            } else {
                result := result + "NO\n";
            }
        }
        
        testCase := testCase + 1;
    }
    
    // Ensure result is not empty if t == 0
    if t == 0 && result == "" {
        result := "\n";
    }
}
// </vc-code>

