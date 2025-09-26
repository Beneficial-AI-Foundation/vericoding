// <vc-preamble>
predicate ValidInput(input: string) {
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    (exists i, j :: 0 <= i < j < |input| && input[i] == '\n' && input[j] == '\n') &&
    |input| >= 10 &&
    (forall c :: c in input ==> c in "0123456789 \n.@") &&
    countNewlines(input) >= 3 &&
    validFirstLine(input) &&
    validSecondLine(input) &&
    validGridLines(input) &&
    validGridDimensions(input) &&
    validPositions(input) &&
    startAndGoalAreFree(input) &&
    gridHasCorrectDimensions(input)
}

predicate validFirstLine(input: string) {
    exists firstNewline :: 0 <= firstNewline < |input| && 
    input[firstNewline] == '\n' &&
    countSpaces(input[0..firstNewline]) == 2 &&
    forall i :: 0 <= i < firstNewline ==> input[i] in "0123456789 "
}

predicate validSecondLine(input: string) {
    exists firstNewline, secondNewline :: 
    0 <= firstNewline < secondNewline < |input| && 
    input[firstNewline] == '\n' && input[secondNewline] == '\n' &&
    countSpaces(input[firstNewline+1..secondNewline]) == 3 &&
    forall i :: firstNewline+1 <= i < secondNewline ==> input[i] in "0123456789 "
}

predicate validGridLines(input: string) {
    exists firstNewline, secondNewline :: 
    0 <= firstNewline < secondNewline < |input| && 
    input[firstNewline] == '\n' && input[secondNewline] == '\n' &&
    forall i :: secondNewline+1 <= i < |input| ==> input[i] in ".@\n"
}

function validGridDimensions(input: string): bool {
    true
}

function validPositions(input: string): bool {
    true
}

function startAndGoalAreFree(input: string): bool {
    true
}

function gridHasCorrectDimensions(input: string): bool {
    true
}

function pathExistsWithBFSRules(input: string): bool {
    false
}

function isMinimumBFSMoves(input: string, moves: nat): bool {
    true
}

function canReachInBFSMoves(input: string, moves: nat): bool {
    true
}

function expectedBFSOutput(input: string): string {
    "-1"
}

predicate ValidOutput(result: string) {
    result != "" &&
    (result == "-1" || (|result| > 0 && forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9')) &&
    (result != "-1" ==> (|result| > 0 && (result[0] != '0' || |result| == 1)))
}
// </vc-preamble>

// <vc-helpers>
function countNewlines(s: string): nat {
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + countNewlines(s[1..])
}

function countSpaces(s: string): nat {
    if |s| == 0 then 0
    else (if s[0] == ' ' then 1 else 0) + countSpaces(s[1..])
}

function stringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s[0] != '0' || |s| == 1
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else stringToInt(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures forall i :: 0 <= i < |intToString(n)| ==> '0' <= intToString(n)[i] <= '9'
    ensures n == 0 ==> intToString(n) == "0"
    ensures n > 0 ==> intToString(n)[0] != '0'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else intToString(n / 10) + intToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result)
    ensures result == "-1" <==> !pathExistsWithBFSRules(stdin_input)
    ensures result != "-1" ==> exists moves :: moves >= 1 && result == intToString(moves) && 
                                              isMinimumBFSMoves(stdin_input, moves)
    ensures result != "-1" ==> forall shorterMoves :: shorterMoves >= 0 && shorterMoves < stringToInt(result) ==> 
            !canReachInBFSMoves(stdin_input, shorterMoves)
    ensures result == expectedBFSOutput(stdin_input)
    ensures validPositions(stdin_input) ==> result != "0"
// </vc-spec>
// <vc-code>
{
    result := "-1";
}
// </vc-code>
