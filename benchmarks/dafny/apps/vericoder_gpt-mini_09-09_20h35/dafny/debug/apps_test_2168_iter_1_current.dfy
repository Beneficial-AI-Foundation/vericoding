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
lemma MaxInSeq_ge(s: seq<int>, idx: int)
  requires |s| > 0
  requires 0 <= idx < |s|
  ensures s[idx] <= MaxInSeq(s)
  decreases |s|
{
  if |s| == 1 {
    // s[0] <= MaxInSeq(s) trivially
  } else {
    var tail := s[1..];
    var m := MaxInSeq(tail);
    if s[0] >= m {
      if idx == 0 {
        // s[0] <= MaxInSeq(s) because MaxInSeq(s) == s[0]
      } else {
        MaxInSeq_ge(tail, idx - 1);
        // From recursion: tail[idx-1] <= m.
        // And s[0] >= m, so s[0] >= tail[idx-1], hence tail[idx-1] <= s[0] == MaxInSeq(s).
      }
    } else {
      // MaxInSeq(s) == m
      MaxInSeq_ge(tail, idx - 1);
      // From recursion: tail[idx-1] <= m == MaxInSeq(s)
    }
  }
}

lemma MaxInSeqOfSeq_ge(s: seq<int>, idx: int)
  requires |s| > 0
  requires 0 <= idx < |s|
  ensures s[idx] <= MaxInSeqOfSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    var tail := s[1..];
    var m := MaxInSeqOfSeq(tail);
    if s[0] >= m {
      if idx == 0 {
      } else {
        MaxInSeqOfSeq_ge(tail, idx - 1);
      }
    } else {
      MaxInSeqOfSeq_ge(tail, idx - 1);
    }
  }
}

lemma CompanyMax_le_Global(companies: seq<seq<int>>, i: int)
  requires |companies| >= 1
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  requires 0 <= i < |companies|
  ensures MaxInSeq(companies[i]) <= GlobalMaxSalary(companies)
  decreases |companies|
{
  var seqOfMax := seq(|companies|, k => MaxInSeqFunc(companies[k]));
  MaxInSeqOfSeq_ge(seqOfMax, i);
  // by definition GlobalMaxSalary(companies) == MaxInSeqOfSeq(seqOfMax)
}

lemma SumOverCompanies_nonneg(companies: seq<seq<int>>, globalMax: int)
  requires |companies| >= 1
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  requires forall k :: 0 <= k < |companies| ==> MaxInSeq(companies[k]) <= globalMax
  ensures SumOverCompanies(companies, globalMax) >= 0
  decreases |companies|
{
  if |companies| == 1 {
    var companyMax := MaxInSeqFunc(companies[0]);
    var increasePerEmployee := globalMax - companyMax;
    // increasePerEmployee >= 0 by precondition
    assert increasePerEmployee >= 0;
    // multiplied by positive count gives >= 0
  } else {
    var companyMax := MaxInSeqFunc(companies[0]);
    var increasePerEmployee := globalMax - companyMax;
    assert increasePerEmployee >= 0;
    SumOverCompanies_nonneg(companies[1..], globalMax);
    // sum of non-negatives is non-negative
  }
}

lemma CalculateMinimumIncrease_nonnegative(companies: seq<seq<int>>)
  requires |companies| >= 1
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  ensures CalculateMinimumIncrease(companies) >= 0
  decreases |companies|
{
  var globalMax := GlobalMaxSalary(companies);
  // Prove for all companies their max <= globalMax
  var k := 0;
  while k < |companies|
    decreases |companies| - k
    invariant 0 <= k <= |companies|
    invariant forall t :: 0 <= t < k ==> MaxInSeq(companies[t]) <= globalMax
  {
    CompanyMax_le_Global(companies, k);
    k := k + 1;
  }
  // Now apply SumOverCompanies_nonneg
  SumOverCompanies_nonneg(companies, globalMax);
}
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
  CalculateMinimumIncrease_nonnegative(companies);
  result := CalculateMinimumIncrease(companies);
}
// </vc-code>

