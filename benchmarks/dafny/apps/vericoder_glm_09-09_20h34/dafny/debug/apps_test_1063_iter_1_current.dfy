predicate isWellFormedInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    if |lines| < 1 then false
    else
        var n := parseInt(lines[0]);
        n >= 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            |lines[i]| >= 1 && |lines[i]| <= 8 &&
            (forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] >= '0' && lines[i][j] <= '9') || lines[i][j] == '?'))
}

ghost predicate hasValidSolution(stdin_input: string)
    requires isWellFormedInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    var n := parseInt(lines[0]);
    if n <= 0 then true
    else
        var inputStrings := lines[1..n+1];
        exists solution :: isValidSequenceSolution(inputStrings, solution)
}

predicate isValidSequenceSolution(input: seq<string>, solution: seq<string>)
{
    |input| == |solution| &&
    (forall i :: 0 <= i < |input| ==> 
        |input[i]| == |solution[i]| &&
        forall j :: 0 <= j < |input[i]| ==> 
            (input[i][j] != '?' ==> input[i][j] == solution[i][j]) &&
            (input[i][j] == '?' ==> solution[i][j] >= '0' && solution[i][j] <= '9')) &&
    (forall i :: 0 <= i < |solution| ==> isValidPositiveInteger(solution[i])) &&
    isStrictlyIncreasingSequence(solution)
}

predicate isValidPositiveInteger(s: string)
{
    |s| >= 1 && 
    (forall i :: 0 <= i < |s| ==> (s[i] >= '0' && s[i] <= '9')) &&
    (|s| == 1 || s[0] != '0')
}

predicate isStrictlyIncreasingSequence(nums: seq<string>)
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

predicate isLexicographicallySmaller(a: string, b: string)
    requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
{
    |a| < |b| || (|a| == |b| && a < b)
}

// <vc-helpers>
function splitLines(s: string): seq<string>
{
    if s == "" then []
    else
        var idx := findChar(s, '\n');
        if idx == -1 then [s] else [s[..idx]] + splitLines(s[idx+1:])
}

function findChar(s: string, c: char): int
{
    if s == "" then -1
    else if s[0] == c then 0
    else
        var rec := findChar(s[1:], c);
        if rec == -1 then -1 else rec + 1
}

function parseInt(s: string): int
    requires forall j :: 0 <= j < |s| ==> s[j] >= '0' && s[j] <= '9'
    requires |s| > 0
    requires |s| == 1 || s[0] != '0'
{
    if |s| == 1 then ord(s[0]) - ord('0')
    else (ord(s[0]) - ord('0')) * 10 + parseInt(s[1:])
}

function parseValue(s: string): int
    requires forall j :: 0 <= j < |s| ==> (s[j] >= '0' && s[j] <= '9') || s[j] == '?'
    requires |s| >= 1
    requires |s| <= 8
    decreases |s|
{
    if s[0] == '?' then 0
    else
        var val := ord(s[0]) - ord('0');
        if |s| == 1 then val
        else val * 10 + parseValue(s[1..])
}

function toDigit(i: int): char
    requires 0 <= i <= 9
{
    chr(ord('0') + i)
}

function replaceQuestionMark(s: string, replacement: char): string
    requires replacement >= '0' && replacement <= '9'
{
    if s == "" then ""
    else (if s[0] == '?' then replacement else s[0]) + replaceQuestionMark(s[1:], replacement)
}

function findMinValidNumber(prev_num: int, length: int): int
    requires prev_num >= 0
    requires length >= 1
    requires length <= 8
{
    var min_val := if length == 1 then 1 else 10;
    var low_bound := prev_num + 1;
    var min_length := if low_bound == 0 then 1 else numDigits(low_bound);
    if min_length < length || (min_length == length && low_bound < calcPower(length)) then
        if min_length < length then calcPower(length - 1)
        else low_bound
    else calcPower(length)
}

function numDigits(n: int): int
    requires n >= 0
{
    if n == 0 then 1
    else if n < 10 then 1
    else 1 + numDigits(n / 10)
}

function calcPower(exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1
    else 10 * calcPower(exp - 1)
}

function constructSolution(prev_num: int, remainder: seq<string>): (result: string, found: bool)
    requires forall i :: 0 <= i < |remainder| ==> |remainder[i]| >= 1 && |remainder[i]| <= 8
    requires forall i :: 0 <= i < |remainder| ==> 
        forall j :: 0 <= j < |remainder[i]| ==> 
            (remainder[i][j] >= '0' && remainder[i][j] <= '9') || remainder[i][j] == '?'
    ensures found ==> prev_num < parseValue(result)
    ensures found ==> |result| > 0
    ensures found ==> isValidPositiveInteger(result)
    decreases |remainder|
{
    if |remainder| == 0 then ("", false)
    else
        var current_attempted := remainder[0];
        var min_candidate := findMinValidNumber(prev_num, |current_attempted|);
        var digit_start := if |current_attempted| == 1 then (if min_candidate > 9 then -1 else min_candidate) else min_candidate;
        var digit_end := calcPower(|current_attempted|) - 1;
        
        if digit_start == -1 then ("", false)
        else
            var (next_sol_valid, next_sol_exists) := checkAndReturnValidSolution(digit_start, digit_end, prev_num, current_attempted, remainder[1:]);
            if next_sol_exists then (next_sol_valid, true)
            else if |remainder| > 1 && |remainder[1]| > |current_attempted| then
                var min_candidate_next := findMinValidNumber(prev_num, |remainder[1]|);
                constructSolution(prev_num, [remainder[0]] + [replaceQuestionMark(remainder[1], toDigit(1))] + remainder[2:])
            else
                ("", false)
}

function checkAndReturnValidSolution(start: int, end: int, prev_num: int, current_pattern: string, remainder: seq<string>): (solution: string, found: bool)
    requires start <= end
    requires prev_num >= 0
    requires |current_pattern| >= 1 && |current_pattern| <= 8
    requires forall i :: 0 <= i < |current_pattern| ==> 
        (current_pattern[i] >= '0' && current_pattern[i] <= '9') || current_pattern[i] == '?'
    requires forall i :: 0 <= i < |remainder| ==> |remainder[i]| >= 1 && |remainder[i]| <= 8
    requires forall i :: 0 <= i < |remainder| ==> 
        forall j :: 0 <= j < |remainder[i]| ==> 
            (remainder[i][j] >= '0' && remainder[i][j] <= '9') || remainder[i][j] == '?'
    ensures found ==> solution == "" || isValidPositiveInteger(solution)
    ensures found ==> prev_num < parseValue(solution)
    decreases end - start
{
    if start > end then ("", false)
    else
        var candidate_str := intToString(start);
        if |candidate_str| != |current_pattern| then checkAndReturnValidSolution(start + 1, end, prev_num, current_pattern, remainder)
        else
            var is_match := true;
            var i := 0;
            while i < |current_pattern| && is_match
                invariant 0 <= i <= |current_pattern|
                invariant is_match ==> (forall k :: 0 <= k < i ==> (current_pattern[k] == '?' || current_pattern[k] == candidate_str[k]))
            {
                if current_pattern[i] != '?' && current_pattern[i] != candidate_str[i] then 
                    is_match := false;
                i := i + 1;
            }
            if !is_match then checkAndReturnValidSolution(start + 1, end, prev_num, current_pattern, remainder)
            else
                var (next_part, next_found) := constructSolution(start, remainder);
                if next_found then (candidate_str, true)
                else if |remainder| > 1 then 
                    checkAndReturnValidSolution(start + 1, end, prev_num, current_pattern, remainder)
                else (candidate_str, true)
}

function intToString(n: int): string
    requires n >= 0
    decreases n
{
    if n < 10 then toDigit(n).ToString()
    else intToString(n / 10) + toDigit(n % 10).ToString()
}

function fillPattern(pattern: string, number: int): string
    requires |pattern| == numDigits(number)
    requires forall i :: 0 <= i < |pattern| ==> 
        (pattern[i] >= '0' && pattern[i] <= '9') || pattern[i] == '?'
{
    var num_str := intToString(number);
    var filled := "";
    var i := 0;
    while i < |pattern|
        invariant 0 <= i <= |pattern|
        invariant |filled| == i
    {
        filled := filled + (if pattern[i] == '?' then num_str[i] else pattern[i]);
        i := i + 1;
    }
    filled
}

function isSequenceValid(nums: seq<string>): bool
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

function trySolveSequence(inputStrings: seq<string>): (result: seq<string>, found: bool)
    requires forall i :: 0 <= i < |inputStrings| ==> |inputStrings[i]| >= 1 && |inputStrings[i]| <= 8
    requires forall i :: 0 <= i < |inputStrings| ==> 
        forall j :: 0 <= j < |inputStrings[i]| ==> 
            (inputStrings[i][j] >= '0' && input_inputStrings[i][j] <= '9') || inputStrings[i][j] == '?'
    ensures found ==> isValidSequenceSolution(inputStrings, result)
{
    if |inputStrings| == 0 then ([], true)
    else
        var (first_num_str, first_found) := findFirstValidNumber(inputStrings[0]);
        if !first_found then ([], false)
        else
            var (rest, rest_found) := trySolveRecursive(parseInt(first_num_str), inputStrings[1:]);
            if rest_found then (first_num_str + rest, true)
            else ([], false)
}

function findFirstValidNumber(pattern: string): (number: string, found: bool)
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures found ==> isValidPositiveInteger(number)
{
    var start := if |pattern| == 1 then 1 else 10;
    var end := calcPower(|pattern|) - 1;
    checkAndReturnValidSolution(start, end, -1, pattern, [])
}

function trySolveRecursive(prev_num: int, remainder: seq<string>): (result: seq<string>, found: bool)
    requires prev_num >= -1
    requires forall i :: 0 <= i < |remainder| ==> |remainder[i]| >= 1 && |remainder[i]| <= 8
    requires forall i :: 0 <= i < |remainder| ==> 
        forall j :: 0 <= j < |remainder[i]| ==> 
            (remainder[i][j] >= '0' && remainder[i][j] <= '9') || remainder[i][j] == '?'
    ensures found ==> |result| == |remainder|
    ensures found ==> isValidSequenceSolution(remainder, result)
    decreases |remainder|
{
    if |remainder| == 0 then ([], true)
    else
        var (current_str, current_found) := findNextValidNumber(prev_num, remainder[0]);
        if !current_found then ([], false)
        else
            var (tail, tail_found) := trySolveRecursive(parseInt(current_str), remainder[1:]);
            if tail_found then ([current_str] + tail, true)
            else ([], false)
}

function findNextValidNumber(prev_num: int, pattern: string): (number: string, found: bool)
    requires prev_num >= 0
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures found ==> isValidPositiveInteger(number)
    ensures found ==> prev_num < parseInt(number)
{
    var len := |pattern|;
    var min_val := findMinValidNumber(prev_num, len);
    var max_val := calcPower(len) - 1;
    if min_val > max_val then ("", false)
    else checkAndReturnValidSolution(min_val, max_val, prev_num, pattern, [])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  var n := parseInt(lines[0]);
  var inputStrings := lines[1..n+1];

  if n == 0 {
    return "YES\n";
  }

  var (solution, found) := trySolveSequence(inputStrings);

  if !found {
    return "NO\n";
  } else {
    var result := "YES\n";
    var i := 0;
    while i < |solution|
      invariant 0 <= i <= |solution|
      invariant |result| == 4 + i * (|solution[0]| + 1)
    {
      result := result + solution[i];
      if i < |solution| - 1 {
        result := result + "\n";
      }
      i := i + 1;
    }
    return result + "\n";
  }
}
// </vc-code>

