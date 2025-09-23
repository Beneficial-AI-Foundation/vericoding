// <vc-preamble>
function validInput(input: string): bool
    requires |input| > 0
{
    exists lines :: parseLines(input) == lines &&
                   |lines| >= 2 &&
                   isPositiveInteger(lines[0]) &&
                   var n := parseInteger(lines[0]);
                   n > 0 && n <= 100000 &&
                   isBillSequence(lines[1], n)
}

function parseLines(input: string): seq<string>
    requires |input| > 0
{
    ["1", "25"]
}

function isPositiveInteger(line: string): bool
{
    true
}

function parseInteger(line: string): int
    requires isPositiveInteger(line)
{
    1
}

function isBillSequence(line: string, expectedCount: int): bool
    requires expectedCount > 0
{
    true
}

function parseInput(input: string): seq<int>
    requires |input| > 0
    requires validInput(input)
    ensures forall i :: 0 <= i < |parseInput(input)| ==> parseInput(input)[i] in {25, 50, 100}
    ensures |parseInput(input)| > 0 ==> |parseInput(input)| <= 100000
{
    var lines := parseLines(input);
    var n := parseInteger(lines[0]);
    parseBills(lines[1], n)
}

function parseBills(line: string, count: int): seq<int>
    requires count >= 0
    ensures |parseBills(line, count)| == count
    ensures forall i :: 0 <= i < count ==> parseBills(line, count)[i] in {25, 50, 100}
{
    seq(count, i => 25)
}

function canServeAllCustomersFromInput(input: string): bool
    requires |input| > 0
    requires validInput(input)
{
    canServeAllCustomers(parseInput(input))
}

function canServeAllCustomers(bills: seq<int>): bool
    requires forall i :: 0 <= i < |bills| ==> bills[i] in {25, 50, 100}
{
    canServeCustomersHelper(bills, 0, 0)
}

function canServeCustomersHelper(bills: seq<int>, change25: int, change50: int): bool
    requires forall i :: 0 <= i < |bills| ==> bills[i] in {25, 50, 100}
    requires change25 >= 0 && change50 >= 0
    decreases |bills|
{
    if |bills| == 0 then true
    else if bills[0] == 25 then
        canServeCustomersHelper(bills[1..], change25 + 1, change50)
    else if bills[0] == 50 then
        if change25 > 0 then
            canServeCustomersHelper(bills[1..], change25 - 1, change50 + 1)
        else
            false
    else
        if change50 > 0 && change25 > 0 then
            canServeCustomersHelper(bills[1..], change25 - 1, change50 - 1)
        else if change25 >= 3 then
            canServeCustomersHelper(bills[1..], change25 - 3, change50)
        else
            false
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> canServeAllCustomersFromInput(stdin_input)
// </vc-spec>
// <vc-code>
{
    var bills := parseInput(stdin_input);

    if |bills| == 0 {
        return "YES\n";
    }

    var change25 := 0;
    var change50 := 0;
    var i := 0;
    var canContinue := true;

    while i < |bills| && canContinue
        invariant 0 <= i <= |bills|
        invariant change25 >= 0 && change50 >= 0
        invariant canContinue <==> canServeCustomersHelper(bills[i..], change25, change50)
        invariant canServeAllCustomers(bills) <==> canServeCustomersHelper(bills[i..], change25, change50)
    {
        if bills[i] == 25 {
            change25 := change25 + 1;
        } else if bills[i] == 50 {
            if change25 > 0 {
                change25 := change25 - 1;
                change50 := change50 + 1;
            } else {
                canContinue := false;
            }
        } else if bills[i] == 100 {
            if change50 > 0 && change25 > 0 {
                change50 := change50 - 1;
                change25 := change25 - 1;
            } else if change25 >= 3 {
                change25 := change25 - 3;
            } else {
                canContinue := false;
            }
        }

        i := i + 1;
    }

    if canContinue {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>
