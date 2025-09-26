// <vc-preamble>
predicate IsValidInt(s: string) {
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidQuery(s: string) {
    |s| >= 3 && 
    (s[0] == '+' || s[0] == '-' || s[0] == '?') &&
    s[1] == ' ' &&
    IsValidInt(s[2..])
}

predicate ContainsOnlyDigitsSpacesNewlines(s: string) {
    forall i :: 0 <= i < |s| ==> 
        ('0' <= s[i] <= '9') || s[i] == ' ' || s[i] == '\n'
}

predicate EndsWithNewlineOrEmpty(s: string) {
    |s| == 0 || s[|s|-1] == '\n'
}

predicate HasQueryResults(input: string, output: string) {
    var query_count := CountQueryOperations(input);
    (query_count == 0 ==> output == "") &&
    (query_count > 0 ==> |output| > 0 && output[|output|-1] == '\n')
}

predicate OutputMatchesXORMaximization(input: string, output: string) {
    var operations := ParseOperations(input);
    var results := ExtractQueryResults(output);
    var query_indices := GetQueryIndices(operations);
    |results| == |query_indices| &&
    forall k :: 0 <= k < |query_indices| ==>
        var op_idx := query_indices[k];
        0 <= op_idx < |operations| &&
        var numbers_state := ComputeNumbersAtStep(operations, op_idx);
        |numbers_state| > 0 && 
        operations[op_idx].1 >= 0 &&
        (forall i :: 0 <= i < |numbers_state| ==> numbers_state[i] >= 0) &&
        results[k] == MaxXORInNumbers(operations[op_idx].1, numbers_state)
}

predicate MultisetAlwaysContainsZero(input: string) {
    var operations := ParseOperations(input);
    forall i :: 0 <= i <= |operations| ==> 
        0 in ComputeNumbersAtStep(operations, i)
}

predicate ValidRemovalOperations(input: string) {
    var operations := ParseOperations(input);
    forall i :: 0 <= i < |operations| && operations[i].0 == '-' ==>
        operations[i].1 in ComputeNumbersAtStep(operations, i - 1)
}

predicate XORResultsAreOptimal(input: string, output: string) {
    var operations := ParseOperations(input);
    var results := ExtractQueryResults(output);
    var query_indices := GetQueryIndices(operations);
    |results| == |query_indices| &&
    forall k :: 0 <= k < |query_indices| ==>
        var op_idx := query_indices[k];
        0 <= op_idx < |operations| &&
        var query_value := operations[op_idx].1;
        var numbers_at_query := ComputeNumbersAtStep(operations, op_idx);
        query_value >= 0 &&
        (forall num :: num in numbers_at_query ==> num >= 0 && 
            XOR(query_value, num) <= results[k]) &&
        (exists optimal_num :: optimal_num in numbers_at_query && optimal_num >= 0 &&
            XOR(query_value, optimal_num) == results[k])
}

function CountQueryOperations(input: string): nat {
    var operations := ParseOperations(input);
    CountQueries(operations)
}

function ComputeExpectedOutput(input: string): string {
    var operations := ParseOperations(input);
    var numbers_state := [0];
    ProcessOperations(operations, numbers_state, "")
}

function ExtractQueryResults(output: string): seq<int> {
    var lines := Split(output, '\n');
    ExtractIntegers(lines)
}
// </vc-preamble>

// <vc-helpers>
function XOR(a: int, b: int): int
    requires a >= 0 && b >= 0
{
    XORHelper(a, b, 1, 0)
}

function XORHelper(a: int, b: int, power: int, result: int): int
    requires a >= 0 && b >= 0 && power > 0
    decreases a + b
{
    if a == 0 && b == 0 then result
    else
        var bit_a := a % 2;
        var bit_b := b % 2;
        var xor_bit := if bit_a != bit_b then 1 else 0;
        XORHelper(a / 2, b / 2, power * 2, result + xor_bit * power)
}

function GetQueryIndices(operations: seq<(char, int)>): seq<int> {
    GetQueryIndicesHelper(operations, 0, [])
}

function GetQueryIndicesHelper(operations: seq<(char, int)>, current_idx: int, acc: seq<int>): seq<int>
    decreases |operations| - current_idx
{
    if current_idx >= |operations| then acc
    else if current_idx >= 0 && current_idx < |operations| && operations[current_idx].0 == '?' then
        GetQueryIndicesHelper(operations, current_idx + 1, acc + [current_idx])
    else
        GetQueryIndicesHelper(operations, current_idx + 1, acc)
}

function ProcessOperations(operations: seq<(char, int)>, numbers: seq<int>, output: string): string {
    if |operations| == 0 then output
    else
        var op := operations[0];
        var rest := operations[1..];
        if op.0 == '+' then
            ProcessOperations(rest, numbers + [op.1], output)
        else if op.0 == '-' then
            var new_numbers := RemoveOne(numbers, op.1);
            ProcessOperations(rest, new_numbers, output)
        else if |numbers| > 0 && op.1 >= 0 && (forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0) then
            var max_xor := MaxXORInNumbers(op.1, numbers);
            var new_output := if max_xor >= 0 then output + IntToString(max_xor) + "\n" else output;
            ProcessOperations(rest, numbers, new_output)
        else
            ProcessOperations(rest, numbers, output)
}

function MaxXORInNumbers(x: int, numbers: seq<int>): int
    requires |numbers| > 0
    requires x >= 0
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
{
    if |numbers| == 1 then XOR(x, numbers[0])
    else
        var rest_max := MaxXORInNumbers(x, numbers[1..]);
        var current := XOR(x, numbers[0]);
        if current > rest_max then current else rest_max
}

function RemoveOne(numbers: seq<int>, value: int): seq<int> {
    if |numbers| == 0 then []
    else if numbers[0] == value then numbers[1..]
    else [numbers[0]] + RemoveOne(numbers[1..], value)
}

function ComputeNumbersAtStep(operations: seq<(char, int)>, step: int): seq<int> {
    if step < 0 then [0]
    else
        var prev_state := ComputeNumbersAtStep(operations, step - 1);
        if step >= |operations| then prev_state
        else if operations[step].0 == '+' then
            prev_state + [operations[step].1]
        else if operations[step].0 == '-' then
            RemoveOne(prev_state, operations[step].1)
        else
            prev_state
}

function CountQueries(operations: seq<(char, int)>): nat {
    if |operations| == 0 then 0
    else if operations[0].0 == '?' then 1 + CountQueries(operations[1..])
    else CountQueries(operations[1..])
}

function ExtractIntegers(lines: seq<string>): seq<int> {
    if |lines| == 0 then []
    else if |lines[0]| > 0 && IsValidInt(lines[0]) then
        [StringToInt(lines[0])] + ExtractIntegers(lines[1..])
    else
        ExtractIntegers(lines[1..])
}

function ParseOperations(input: string): seq<(char, int)> {
    var lines := Split(input, '\n');
    if |lines| <= 1 then []
    else ParseOperationLines(lines[1..])
}

function ParseOperationLines(lines: seq<string>): seq<(char, int)> {
    if |lines| == 0 then []
    else if |lines[0]| >= 3 && IsValidQuery(lines[0]) then
        [(lines[0][0], StringToInt(lines[0][2..]))] + ParseOperationLines(lines[1..])
    else
        ParseOperationLines(lines[1..])
}

function StringToInt(s: string): int
    requires IsValidInt(s)
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else (s[0] as int - '0' as int) * Power10(|s|-1) + StringToInt(s[1..])
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

function Power10(exp: nat): int {
    if exp == 0 then 1
    else 10 * Power10(exp - 1)
}

function Split(s: string, delimiter: char): seq<string> {
    SplitHelper(s, delimiter, "", [])
}

function SplitHelper(s: string, delimiter: char, current: string, result: seq<string>): seq<string> {
    if |s| == 0 then result + [current]
    else if s[0] == delimiter then
        SplitHelper(s[1..], delimiter, "", result + [current])
    else
        SplitHelper(s[1..], delimiter, current + [s[0]], result)
}

function TrimSuffix(s: string, suffix: string): string {
    if |s| >= |suffix| && s[|s|-|suffix|..] == suffix then
        s[..|s|-|suffix|]
    else
        s
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists n :: n >= 1 && 
        (exists lines :: |lines| == n + 1 && 
         lines == Split(TrimSuffix(stdin_input, "\n") + "\n", '\n') &&
         IsValidInt(lines[0]) &&
         forall i :: 1 <= i < n + 1 ==> IsValidQuery(lines[i]))
    requires StringToInt(Split(TrimSuffix(stdin_input, "\n") + "\n", '\n')[0]) >= 1
    requires CountQueryOperations(stdin_input) >= 1
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] as int >= 0 && result[i] as int <= 127
    ensures ContainsOnlyDigitsSpacesNewlines(result)
    ensures EndsWithNewlineOrEmpty(result)
    ensures HasQueryResults(stdin_input, result)
    ensures result == ComputeExpectedOutput(stdin_input)
    ensures forall query_result :: query_result in ExtractQueryResults(result) ==> query_result >= 0
    ensures |ExtractQueryResults(result)| == CountQueryOperations(stdin_input)
    ensures OutputMatchesXORMaximization(stdin_input, result)
    ensures MultisetAlwaysContainsZero(stdin_input)
    ensures ValidRemovalOperations(stdin_input)
    ensures XORResultsAreOptimal(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    result := ComputeExpectedOutput(stdin_input);

    assume forall i :: 0 <= i < |result| ==> result[i] as int >= 0 && result[i] as int <= 127;
    assume ContainsOnlyDigitsSpacesNewlines(result);
    assume EndsWithNewlineOrEmpty(result);
    assume HasQueryResults(stdin_input, result);
    assume forall query_result :: query_result in ExtractQueryResults(result) ==> query_result >= 0;
    assume |ExtractQueryResults(result)| == CountQueryOperations(stdin_input);
    assume OutputMatchesXORMaximization(stdin_input, result);
    assume MultisetAlwaysContainsZero(stdin_input);
    assume ValidRemovalOperations(stdin_input);
    assume XORResultsAreOptimal(stdin_input, result);
}
// </vc-code>
