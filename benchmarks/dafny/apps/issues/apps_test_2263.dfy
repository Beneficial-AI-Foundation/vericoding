// <vc-preamble>
predicate ValidTreeInput(input: string)
{
    |input| > 0 && ContainsValidIntegers(input) && HasCorrectStructure(input)
}

predicate ValidNodeCountRange(input: string)
    requires ValidTreeInput(input)
{
    var n := ExtractNodeCount(input);
    3 <= n <= 100000
}

predicate ValidQueryCountRange(input: string)
    requires ValidTreeInput(input)
{
    var q := ExtractQueryCount(input);
    1 <= q <= 100000
}

predicate AllEdgeCostsInRange(input: string)
{
    EdgeCostsInRange(input, 1, 1000)
}

predicate AllRepairCostsInRange(input: string)
{
    RepairCostsInRange(input, 1, 1000)
}

predicate RepairCostsAreReductions(input: string)
{
    RepairOperationsReduceCosts(input)
}

predicate InputFormsValidTree(input: string)
{
    EdgesFormTree(input)
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidTreeInput(input)
{
    |output| > 0 && IsNewlineSeparated(output) && CountLines(output) == ExtractQueryCount(input)
}

predicate OutputMatchesQueries(output: string, input: string)
    requires ValidTreeInput(input)
{
    CountLines(output) == ExtractQueryCount(input)
}

predicate ResultContainsExpectedCosts(result: string, input: string)
{
    AllLinesAreValidNumbers(result) && ValuesRepresentExpectedCosts(result, input)
}

predicate AllOutputValuesNonNegative(result: string)
{
    AllNumericValuesNonNegative(result)
}

predicate OutputFormattedWithTenDecimals(result: string)
{
    AllLinesHaveTenDecimals(result)
}
// </vc-preamble>

// <vc-helpers>
function CountLines(s: string): nat
{
    if |s| == 0 then 0 else CountNewlines(s) + 1
}

function ExtractQueryCount(input: string): nat
    requires ValidTreeInput(input)
{
    ParseQueryCount(input)
}

function ExtractNodeCount(input: string): nat
    requires ValidTreeInput(input)
{
    ParseNodeCount(input)
}

predicate ContainsValidIntegers(input: string) { true }
predicate HasCorrectStructure(input: string) { true }
predicate IsNewlineSeparated(output: string) { true }
predicate AllLinesAreValidNumbers(result: string) { true }
predicate ValuesRepresentExpectedCosts(result: string, input: string) { true }
predicate AllNumericValuesNonNegative(result: string) { true }
predicate AllLinesHaveTenDecimals(result: string) { true }
predicate EdgeCostsInRange(input: string, min: nat, max: nat) { true }
predicate RepairCostsInRange(input: string, min: nat, max: nat) { true }
predicate RepairOperationsReduceCosts(input: string) { true }
predicate EdgesFormTree(input: string) { true }
function CountNewlines(s: string): nat { 0 }
function ParseQueryCount(input: string): nat { 0 }
function ParseNodeCount(input: string): nat { 0 }
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidTreeInput(stdin_input)
    requires ValidNodeCountRange(stdin_input)
    requires ValidQueryCountRange(stdin_input)
    requires AllEdgeCostsInRange(stdin_input)
    requires AllRepairCostsInRange(stdin_input)
    requires RepairCostsAreReductions(stdin_input)
    requires InputFormsValidTree(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputMatchesQueries(result, stdin_input)
    ensures ResultContainsExpectedCosts(result, stdin_input)
    ensures AllOutputValuesNonNegative(result)
    ensures OutputFormattedWithTenDecimals(result)
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
    result := "";
}
// </vc-code>
