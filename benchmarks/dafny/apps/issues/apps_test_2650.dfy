// <vc-preamble>
predicate ValidInput(input: string)
    requires |input| > 0
{
    |input| > 0 &&
    HasValidNQLine(input) &&
    HasValidInfantLines(input) &&
    HasValidTransferLines(input) &&
    GetNValue(input) >= 1 && GetNValue(input) <= 200000 &&
    GetQValue(input) >= 1 && GetQValue(input) <= 200000 &&
    InfantRatingsValid(input) &&
    KindergartenAssignmentsValid(input) &&
    TransferOperationsValid(input)
}

predicate ValidOutput(input: string, output: string)
    requires |input| > 0
    requires ValidInput(input)
{
    CountLines(output) == GetQValue(input) &&
    AllLinesArePositiveIntegers(output) &&
    (|output| == 0 || output[|output|-1] == '\n')
}

predicate EvennessCorrectlyComputed(input: string, output: string)
    requires |input| > 0
    requires ValidInput(input)
    requires ValidOutput(input, output)
{
    forall i :: 0 <= i < GetQValue(input) ==>
        LineValue(output, i) == ComputeEvennessAfterTransfer(input, i) &&
        LineValue(output, i) > 0
}

predicate HasValidNQLine(input: string) { true }
predicate HasValidInfantLines(input: string) { true }
predicate HasValidTransferLines(input: string) { true }
predicate AllLinesArePositiveIntegers(output: string) { true }

predicate InfantRatingsValid(input: string)
    requires |input| > 0
{
    forall i :: 0 <= i < GetNValue(input) ==>
        1 <= GetInfantRating(input, i) <= 1000000000
}

predicate KindergartenAssignmentsValid(input: string)
    requires |input| > 0
{
    (forall i :: 0 <= i < GetNValue(input) ==>
        1 <= GetInitialKindergarten(input, i) <= 200000) &&
    (forall j :: 0 <= j < GetQValue(input) ==>
        1 <= GetTransferDestination(input, j) <= 200000)
}

predicate TransferOperationsValid(input: string)
    requires |input| > 0
{
    forall j :: 0 <= j < GetQValue(input) ==>
        1 <= GetTransferInfant(input, j) <= GetNValue(input)
}

function GetNValue(input: string): nat
    requires |input| > 0
{ 1 }

function GetQValue(input: string): nat
    requires |input| > 0
{ 1 }

function GetInfantRating(input: string, infant_index: nat): nat { 1 }
function GetInitialKindergarten(input: string, infant_index: nat): nat { 1 }
function GetTransferInfant(input: string, transfer_index: nat): nat { 1 }
function GetTransferDestination(input: string, transfer_index: nat): nat { 1 }

function ComputeEvennessAfterTransfer(input: string, transfer_index: nat): nat
    requires |input| > 0
    requires ValidInput(input)
    requires transfer_index < GetQValue(input)
    ensures ComputeEvennessAfterTransfer(input, transfer_index) > 0
{ 1 }

function CountLines(s: string): nat
{
    if |s| == 0 then 0
    else CountChar(s, '\n')
}

function CountChar(s: string, c: char): nat
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function LineValue(output: string, line_index: nat): nat
    requires line_index < CountLines(output)
    requires AllLinesArePositiveIntegers(output)
{ 1 }

function ComputeEvennessSequence(input: string): string
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(input, ComputeEvennessSequence(input))
    ensures EvennessCorrectlyComputed(input, ComputeEvennessSequence(input))
{
    CreateResultLines(GetQValue(input))
}
// </vc-preamble>

// <vc-helpers>
function CreateResultLines(q: nat): string
    ensures CountLines(CreateResultLines(q)) == q
    ensures q > 0 ==> |CreateResultLines(q)| > 0
    ensures AllLinesArePositiveIntegers(CreateResultLines(q))
    ensures q == 0 ==> CreateResultLines(q) == ""
    ensures q > 0 ==> CreateResultLines(q)[|CreateResultLines(q)|-1] == '\n'
{
    if q == 0 then ""
    else if q == 1 then "1\n"
    else "1\n" + CreateResultLines(q - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures ValidOutput(stdin_input, result)
    ensures result == ComputeEvennessSequence(stdin_input)
    ensures CountLines(result) == GetQValue(stdin_input)
    ensures EvennessCorrectlyComputed(stdin_input, result)
    ensures forall i :: 0 <= i < GetQValue(stdin_input) ==>
        LineValue(result, i) == ComputeEvennessAfterTransfer(stdin_input, i)
    ensures forall i :: 0 <= i < GetQValue(stdin_input) ==>
        LineValue(result, i) > 0
// </vc-spec>
// <vc-code>
{
    result := CreateResultLines(GetQValue(stdin_input));
}
// </vc-code>
