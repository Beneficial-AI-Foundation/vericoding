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

function toDigit(i: int): char
    requires 0 <= i <= 9
{
    chr(ord('0') + i)
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

function intToString(n: int): string
    requires n >= 0
    decreases n
{
    if n < 10 then [toDigit(n)]
    else intToString(n / 10) + [toDigit(n % 10)]
}

function isSequenceValid(nums: seq<string>): bool
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

function trySolveSequence(inputStrings: seq<string>) returns (result: seq<string>, found: bool)
    requires forall i :: 0 <= i < |inputStrings| ==> |inputStrings[i]| >= 1 && |inputStrings[i]| <= 8
    requires forall i :: 0 <= i < |inputStrings| ==> 
        forall j :: 0 <= j < |inputStrings[i]| ==> 
            (inputStrings[i][j] >= '0' && inputStrings[i][j] <= '9') || inputStrings[i][j] == '?'
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

function findFirstValidNumber(pattern: string) returns (number: string, found: bool)
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures found ==> isValidPositiveInteger(number)
{
    var start := if |pattern| == 1 then 1 else 10;
    var end := calcPower(|pattern|) - 1;
    checkAndReturnValidSolution(start, end, -1, pattern, [])
}

function trySolveRecursive(prev_num: int, remainder: seq<string>) returns (result: seq<string>, found: bool)
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
            var (tail,
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
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

function toDigit(i: int): char
    requires 0 <= i <= 9
{
    chr(ord('0') + i)
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

function intToString(n: int): string
    requires n >= 0
    decreases n
{
    if n < 10 then [toDigit(n)]
    else intToString(n / 10) + [toDigit(n % 10)]
}

function isSequenceValid(nums: seq<string>): bool
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

function trySolveSequence(inputStrings: seq<string>) returns (result: seq<string>, found: bool)
    requires forall i :: 0 <= i < |inputStrings| ==> |inputStrings[i]| >= 1 && |inputStrings[i]| <= 8
    requires forall i :: 0 <= i < |inputStrings| ==> 
        forall j :: 0 <= j < |inputStrings[i]| ==> 
            (inputStrings[i][j] >= '0' && inputStrings[i][j] <= '9') || inputStrings[i][j] == '?'
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

function findFirstValidNumber(pattern: string) returns (number: string, found: bool)
    requires |pattern| >= 1 && |pattern| <= 8
    requires forall j :: 0 <= j < |pattern| ==> 
        (pattern[j] >= '0' && pattern[j] <= '9') || pattern[j] == '?'
    ensures found ==> isValidPositiveInteger(number)
{
    var start := if |pattern| == 1 then 1 else 10;
    var end := calcPower(|pattern|) - 1;
    checkAndReturnValidSolution(start, end, -1, pattern, [])
}

function trySolveRecursive(prev_num: int, remainder: seq<string>) returns (result: seq<string>, found: bool)
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
            var (tail,
// </vc-code>

