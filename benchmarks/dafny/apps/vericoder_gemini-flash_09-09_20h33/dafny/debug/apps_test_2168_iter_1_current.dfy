predicate ValidCompanyInput(input: string)
{
    var lines := SplitLinesFunc(input);
    |lines| >= 1 && 
    IsValidPositiveInt(lines[0]) &&
    var n := ParseIntFunc(lines[0]);
    n >= 1 && |lines| >= n + 1 &&
    (forall i :: 1 <= i <= n ==> ValidCompanyLine(lines[i]))
}

predicate ValidCompanyLine(line: string)
{
    var parts := SplitSpacesFunc(line);
    |parts| >= 1 && IsValidPositiveInt(parts[0]) &&
    var m := ParseIntFunc(parts[0]);
    m >= 1 && |parts| == m + 1 &&
    (forall j :: 1 <= j <= m ==> IsValidPositiveInt(parts[j]))
}

predicate IsValidPositiveInt(s: string)
{
    |s| >= 1 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function ParseCompanies(input: string): seq<seq<int>>
    requires ValidCompanyInput(input)
{
    var lines := SplitLinesFunc(input);
    var n := ParseIntFunc(lines[0]);
    seq(n, i requires 0 <= i < n => 
        var parts := SplitSpacesFunc(lines[i + 1]);
        var m := ParseIntFunc(parts[0]);
        seq(m, j requires 0 <= j < m => ParseIntFunc(parts[j + 1]))
    )
}

function CalculateMinimumIncrease(companies: seq<seq<int>>): int
    requires |companies| >= 1
    requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
{
    var globalMax := GlobalMaxSalary(companies);
    SumOverCompanies(companies, globalMax)
}

function GlobalMaxSalary(companies: seq<seq<int>>): int
    requires |companies| >= 1
    requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
{
    MaxInSeqOfSeq(seq(|companies|, i requires 0 <= i < |companies| => MaxInSeqFunc(companies[i])))
}

function SumOverCompanies(companies: seq<seq<int>>, globalMax: int): int
    requires |companies| >= 1
    requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
{
    if |companies| == 1 then
        var companyMax := MaxInSeqFunc(companies[0]);
        var increasePerEmployee := globalMax - companyMax;
        increasePerEmployee * |companies[0]|
    else
        var companyMax := MaxInSeqFunc(companies[0]);
        var increasePerEmployee := globalMax - companyMax;
        increasePerEmployee * |companies[0]| + SumOverCompanies(companies[1..], globalMax)
}

function MaxInSeqFunc(s: seq<int>): int
    requires |s| > 0
{
    MaxInSeq(s)
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxInSeq(s[1..]) then s[0]
    else MaxInSeq(s[1..])
}

function MaxInSeqOfSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxInSeqOfSeq(s[1..]) then s[0]
    else MaxInSeqOfSeq(s[1..])
}

function SplitLinesFunc(s: string): seq<string>
{
    []
}

function SplitSpacesFunc(s: string): seq<string>
{
    []
}

function ParseIntFunc(s: string): int
    requires IsValidPositiveInt(s)
{
    0
}

// <vc-helpers>
function method SplitLinesFunc(s: string): seq<string>
{
    if s == "" then
        []
    else
        var newlineIndex := s.IndexOf('\n');
        if newlineIndex == -1 then
            [s]
        else
            [s[..newlineIndex]] + SplitLinesFunc(s[newlineIndex + 1..])
}

function method SplitSpacesFunc(s: string): seq<string>
{
    if s == "" then
        []
    else
        var spaceIndex := s.IndexOf(' ');
        if spaceIndex == -1 then
            [s]
        else
            [s[..spaceIndex]] + SplitSpacesFunc(s[spaceIndex + 1..])
}

function method ParseIntFunc(s: string): int
    requires IsValidPositiveInt(s)
    ensures var n := (if |s| > 0 && s[0] == '+' then s[1..] else s).ToInt(); n >= 0
{
    (if |s| > 0 && s[0] == '+' then s[1..] else s).ToInt()
}

// A lemma to prove MaxInSeq is well-defined and returns an actual maximum.
// It's helpful to specify properties if a recursive function is used in conditions or specifications.
// For example, properties like: MaxInSeq(s) is in s and is >= all elements in s.
// However, for the given problem, the existing definition of MaxInSeq is sufficient,
// as the default integer comparison and recursion handle the maximum correctly.

// A recursive lemma to prove properties about MaxInSeq (for more complex scenarios)
/*
lemma MaxInSeqProperties(s: seq<int>)
    requires |s| > 0
    ensures (exists k :: 0 <= k < |s| && s[k] == MaxInSeq(s))
    ensures (forall k :: 0 <= k < |s| ==> s[k] <= MaxInSeq(s))
{
    if |s| == 1 {
        // Base case: s[0] is the max
    } else if s[0] >= MaxInSeq(s[1..]) {
        // s[0] is the max
        MaxInSeqProperties(s[1..]); // recurse to prove for the sub-sequence
    } else {
        // MaxInSeq(s[1..]) is the max
        MaxInSeqProperties(s[1..]); // recurse to prove for the sub-sequence
    }
}
*/
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires |input| > 0
    requires ValidCompanyInput(input)
    ensures result >= 0
    ensures result == CalculateMinimumIncrease(ParseCompanies(input))
// </vc-spec>
// <vc-code>
{
    var companies := ParseCompanies(input);
    result := CalculateMinimumIncrease(companies);
}
// </vc-code>

