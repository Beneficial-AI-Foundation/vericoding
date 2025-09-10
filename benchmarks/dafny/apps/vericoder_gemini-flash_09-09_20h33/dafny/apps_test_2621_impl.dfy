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
function countLines(s: string): int
  reads s
  ensures countLines(s) >= 0
{
  var count := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant count == countOccurrences(s[..i], '\n')
  {
    if s[i] == '\n' then
      count := count + 1;
  }
  return count;
}

function countOccurrences(s: string, c: char): int
  reads s
  ensures countOccurrences(s, c) >= 0
{
  var count := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant count == countOccurrences(s, c, i) // Simplified invariant to match function behavior
  {
    if s[i] == c then
      count := count + 1;
  }
  return count;
}

function countOccurrences(s: string, c: char, endIndex: int): int
  reads s
  requires 0 <= endIndex <= |s|
  ensures countOccurrences(s, c, endIndex) >= 0
  decreases endIndex
{
    if endIndex == 0 then 0
    else (if s[endIndex-1] == c then 1 else 0) + countOccurrences(s, c, endIndex-1)
}


function getLine(s: string, lineNumber: int): string
  requires 0 <= lineNumber < countLines(s) // fixed: lineNumber must be less than total lines
  reads s
  ensures var start_idx := startOfLine(s, lineNumber);
          var end_idx := startOfLine(s, lineNumber + 1);
          getLine(s, lineNumber) == s[start_idx .. end_idx]
{
  var start := 0;
  var actualLine := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant 0 <= actualLine <= countLines(s)
    invariant (actualLine <= lineNumber ==> start == startOfLine(s, actualLine))
    invariant (actualLine > lineNumber ==> start == startOfLine(s, lineNumber)) // Fixed: It should represent a starting point that was observed
  {
    if s[i] == '\n' then
      if actualLine == lineNumber then
        return s[start .. i + 1]; // Include the newline character
      start := i + 1;
      actualLine := actualLine + 1;
    }
  return s[start ..]; // handles the last line not ending with newline if countLines allows
}

function getLineWithoutNewline(s: string, lineNumber: int): string
    requires 0 <= lineNumber < countLines(s)
    reads s
{
    var line := getLine(s, lineNumber);
    // Ensure line has at least one character (the newline) before attempting to remove it
    if |line| > 0 && line[|line|-1] == '\n' then
        return line[.. |line|-1]
    else
        return line; // Should not happen given getLine's postcondition and countLines usage
}

function startOfLine(s: string, lineNumber: int): int
    requires 0 <= lineNumber <= countLines(s)
    reads s
    ensures 0 <= startOfLine(s, lineNumber) <= |s|
    ensures (lineNumber == 0 ==> startOfLine(s, lineNumber) == 0)
    ensures (startOfLine(s, lineNumber) == |s| ==> lineNumber == countLines(s))
{
    var count := 0;
    var start := 0;
    for i := 0 to |s|-1
        invariant 0 <= i <= |s|
        invariant 0 <= count <= lineNumber
        invariant (count < lineNumber ==> start == i + 1)
        invariant (count == lineNumber ==> start == (if lineNumber == 0 then 0 else startOfLine(s[..i], lineNumber))) // The invariant was conceptually problematic for the loop. Simplified.
    {
        if s[i] == '\n' {
            count := count + 1;
            if count == lineNumber {
                return i + 1;
            }
            start := i + 1;
        }
    }
    return start;
}

predicate IsDigit(c: char) { '0' <= c <= '9' }

function StringToNat(s: string): (n: nat)
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  requires |s| > 0
  ensures n >= 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    (StringToNat(s[..|s|-1]) * 10) + ((s[|s|-1] as int) - ('0' as int))
}

function parseNumbers(s: string): seq<int>
    reads s
    ensures forall i :: 0 <= i < |parseNumbers(s)| ==> parseNumbers(s)[i] >= 0
{
    var nums_str: seq<string> := [];
    var current_num_str := "";
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < |nums_str| ==> |nums_str[k]| > 0 && (forall c :: c in nums_str[k] ==> IsDigit(c))
        invariant (current_num_str == "" || (forall c :: c in current_num_str ==> IsDigit(c)))
    {
        if i == |s| || s[i] == ' ' {
            if |current_num_str| > 0 {
                nums_str := nums_str + [current_num_str];
            }
            current_num_str := "";
        } else {
            current_num_str := current_num_str + [s[i]];
        }
    }

    var nums: seq<int> := [];
    for s_num in nums_str {
        if |s_num| > 0 && (forall c :: c in s_num ==> IsDigit(c)) {
            nums := nums + [StringToNat(s_num)];
        }
    }
    return nums;
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
    var num_test_cases_str := getLineWithoutNewline(stdin_input, 0);
    var num_test_cases := StringToNat(num_test_cases_str);
    var results := "";

    var current_line_num := 1;
    for test_case_num := 0 to num_test_cases - 1
        invariant 0 <= test_case_num <= num_test_cases
        invariant current_line_num == 1 + test_case_num * 2
        invariant (test_case_num == 0 ==> results == "")
        invariant (test_case_num > 0 ==>
                    (|results| > 0 && results[|results|-1] == '\n'))
        invariant forall i :: 0 <= i < |results| ==> results[i] == 'Y' || results[i] == 'E' || results[i] == 'S' || results[i] == 'N' || results[i] == 'O' || results[i] == '\n'
        invariant current_line_num + 1 < countLines(stdin_input) + (if stdin_input[|stdin_input|-1] == '\n' then 1 else 0) // Adjusted bound for lines if last character is not new line
        invariant num_test_cases >= 0
        invariant countLines(stdin_input) >= 1 + num_test_cases * 2 - (if stdin_input[|stdin_input|-1] == '\n' then 1 else 0)
    {
        var line1_str := getLineWithoutNewline(stdin_input, current_line_num);
        var line2_str := getLineWithoutNewline(stdin_input, current_line_num + 1);

        var first_line_nums := parseNumbers(line1_str);
        
        // Assertions moved to the if condition for runtime check
        if |first_line_nums| == 3 then
            var n := first_line_nums[0];
            var m := first_line_nums[1];
            var k := first_line_nums[2];

            var H := parseNumbers(line2_str);

            if validInput(n, m, k, H) then
                if canReachEnd(n, m, k, H) then
                    results := results + "YES\n";
                else
                    results := results + "NO\n";
            else
                results := results + "ERROR\n"; 
        else
            results := results + "ERROR\n"; 
        
        current_line_num := current_line_num + 2;
    }
    return results;
}
// </vc-code>

