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
function parseNumber(s: string, start: int): (int, int)
    requires 0 <= start <= |s|
    ensures var (num, nextPos) := parseNumber(s, start); nextPos >= start && nextPos <= |s|
    decreases |s| - start
{
    if start >= |s| then (0, start)
    else if s[start] < '0' || s[start] > '9' then (0, start)
    else
        var digit := s[start] as int - '0' as int;
        if start + 1 >= |s| || s[start + 1] < '0' || s[start + 1] > '9' then
            (digit, start + 1)
        else
            var (restNum, nextPos) := parseNumber(s, start + 1);
            (digit * pow10(nextPos - start - 1) + restNum, nextPos)
}

function pow10(n: int): int
    requires n >= 0
    ensures pow10(n) >= 1
    decreases n
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

function skipWhitespace(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures skipWhitespace(s, pos) >= pos && skipWhitespace(s, pos) <= |s|
    decreases |s| - pos
{
    if pos >= |s| then pos
    else if s[pos] == ' ' || s[pos] == '\t' then skipWhitespace(s, pos + 1)
    else pos
}

function skipToNextLine(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures skipToNextLine(s, pos) >= pos && skipToNextLine(s, pos) <= |s|
    decreases |s| - pos
{
    if pos >= |s| then pos
    else if s[pos] == '\n' then pos + 1
    else skipToNextLine(s, pos + 1)
}

function parseSequence(s: string, pos: int, count: int): (seq<int>, int)
    requires 0 <= pos <= |s|
    requires count >= 0
    ensures |parseSequence(s, pos, count).0| <= count && parseSequence(s, pos, count).1 >= pos && parseSequence(s, pos, count).1 <= |s|
    decreases count
{
    if count == 0 then ([], pos)
    else
        var newPos := skipWhitespace(s, pos);
        if newPos >= |s| then ([], newPos)
        else
            var (num, afterNum) := parseNumber(s, newPos);
            var (restSeq, finalPos) := parseSequence(s, afterNum, count - 1);
            ([num] + restSeq, finalPos)
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
    var pos := 0;
    var (t_raw, newPos) := parseNumber(stdin_input, pos);
    pos := skipToNextLine(stdin_input, newPos);
    
    var t := if t_raw >= 0 then t_raw else 0;
    
    result := "";
    var testCase := 0;
    
    while testCase < t && pos < |stdin_input|
        invariant 0 <= testCase <= t
        invariant 0 <= pos <= |stdin_input|
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> result[i] == 'Y' || result[i] == 'E' || result[i] == 'S' || result[i] == 'N' || result[i] == 'O' || result[i] == '\n'
        invariant result == "" || result[|result|-1] == '\n'
    {
        var startPos := skipWhitespace(stdin_input, pos);
        if startPos >= |stdin_input| { break; }
        
        var (n, pos1) := parseNumber(stdin_input, startPos);
        var pos2 := skipWhitespace(stdin_input, pos1);
        if pos2 >= |stdin_input| { break; }
        
        var (m, pos3) := parseNumber(stdin_input, pos2);
        var pos4 := skipWhitespace(stdin_input, pos3);
        if pos4 >= |stdin_input| { break; }
        
        var (k, pos5) := parseNumber(stdin_input, pos4);
        pos := skipToNextLine(stdin_input, pos5);
        
        if pos >= |stdin_input| { break; }
        
        if n >= 0 {
            var (H, newPos2) := parseSequence(stdin_input, pos, n);
            pos := skipToNextLine(stdin_input, newPos2);
            
            if n >= 1 && |H| == n && m >= 0 && k >= 0 && 
               (forall i :: 0 <= i < |H| ==> H[i] >= 0) {
                if canReachEnd(n, m, k, H) {
                    result := result + "YES\n";
                } else {
                    result := result + "NO\n";
                }
            } else {
                result := result + "NO\n";
            }
        } else {
            result := result + "NO\n";
            pos := skipToNextLine(stdin_input, pos);
        }
        
        testCase := testCase + 1;
    }
}
// </vc-code>

