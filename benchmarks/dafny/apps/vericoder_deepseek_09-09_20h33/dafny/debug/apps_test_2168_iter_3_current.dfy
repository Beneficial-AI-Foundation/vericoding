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
lemma MaxInSeqLemma(s: seq<int>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> MaxInSeq(s) >= s[i]
  decreases |s|
{
  if |s| > 1 {
    MaxInSeqLemma(s[1..]);
    if s[0] >= MaxInSeq(s[1..]) {
      // s[0] is the max
      forall i | 0 <= i < |s| 
        ensures MaxInSeq(s) >= s[i]
      {
        if i == 0 {
          assert MaxInSeq(s) == s[0];
        } else {
          assert MaxInSeq(s[1..]) >= s[i];
          assert MaxInSeq(s) == s[0] >= MaxInSeq(s[1..]) >= s[i];
        }
      }
    } else {
      // MaxInSeq(s[1..]) is the max
      forall i | 0 <= i < |s| 
        ensures MaxInSeq(s) >= s[i]
      {
        if i == 0 {
          assert MaxInSeq(s) == MaxInSeq(s[1..]) >= s[0];
        } else {
          assert MaxInSeq(s[1..]) >= s[i];
          assert MaxInSeq(s) == MaxInSeq(s[1..]) >= s[i];
        }
      }
    }
  }
}

lemma MaxInSeqEqualsAnother(s: seq<int>)
  requires |s| > 0
  ensures MaxInSeq(s) == MaxInSeqFunc(s)
{
}

lemma MaxInSeqOfSeqLemma(s: seq<int>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> MaxInSeqOfSeq(s) >= s[i]
  decreases |s|
{
  if |s| > 1 {
    MaxInSeqOfSeqLemma(s[1..]);
    if s[0] >= MaxInSeqOfSeq(s[1..]) {
      forall i | 0 <= i < |s| 
        ensures MaxInSeqOfSeq(s) >= s[i]
      {
        if i == 0 {
          assert MaxInSeqOfSeq(s) == s[0];
        } else {
          assert MaxInSeqOfSeq(s[1..]) >= s[i];
          assert MaxInSeqOfSeq(s) == s[0] >= MaxInSeqOfSeq(s[1..]) >= s[i];
        }
      }
    } else {
      forall i | 0 <= i < |s| 
        ensures MaxInSeqOfSeq(s) >= s[i]
      {
        if i == 0 {
          assert MaxInSeqOfSeq(s) == MaxInSeqOfSeq(s[1..]) >= s[0];
        } else {
          assert MaxInSeqOfSeq(s[1..]) >= s[i];
          assert MaxInSeqOfSeq(s) == MaxInSeqOfSeq(s[1..]) >= s[i];
        }
      }
    }
  }
}

lemma GlobalMaxSalaryLemma(companies: seq<seq<int>>)
  requires |companies| >= 1
  requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
  ensures forall i, j :: 0 <= i < |companies| && 0 <= j < |companies[i]| ==>
           GlobalMaxSalary(companies) >= companies[i][j]
{
  var maxSeq := seq(|companies|, i requires 0 <= i < |companies| => MaxInSeqFunc(companies[i]));
  MaxInSeqOfSeqLemma(maxSeq);
  
  forall i, j | 0 <= i < |companies| && 0 <= j < |companies[i]|
    ensures GlobalMaxSalary(companies) >= companies[i][j]
  {
    MaxInSeqLemma(companies[i]);
    assert MaxInSeqFunc(companies[i]) >= companies[i][j];
    assert maxSeq[i] == MaxInSeqFunc(companies[i]);
    assert MaxInSeqOfSeq(maxSeq) >= maxSeq[i];
  }
}

lemma SumOverCompaniesNonNegative(companies: seq<seq<int>>, globalMax: int)
  requires |companies| >= 1
  requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
  requires forall i, j :: 0 <= i < |companies| && 0 <= j < |companies[i]| ==> globalMax >= companies[i][j]
  ensures SumOverCompanies(companies, globalMax) >= 0
  decreases companies
{
  if |companies| == 1 {
    var companyMax := MaxInSeqFunc(companies[0]);
    assert globalMax >= companyMax;
  } else {
    var companyMax := MaxInSeqFunc(companies[0]);
    assert globalMax >= companyMax;
    SumOverCompaniesNonNegative(companies[1..], globalMax);
  }
}

lemma CompanyMaxLemma(companies: seq<seq<int>>, globalMax: int)
  requires |companies| >= 1
  requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
  requires forall i, j :: 0 <= i < |companies| && 0 <= j < |companies[i]| ==> globalMax >= companies[i][j]
  ensures forall company :: company in companies ==> globalMax >= MaxInSeqFunc(company)
{
  forall company | company in companies
    ensures globalMax >= MaxInSeqFunc(company)
  {
    MaxInSeqLemma(company);
    assert forall j :: 0 <= j < |company| ==> MaxInSeqFunc(company) >= company[j];
    assert exists j :: 0 <= j < |company| && MaxInSeqFunc(company) == company[j];
  }
}

lemma SumOverCompaniesCorrect(companies: seq<seq<int>>, globalMax: int)
  requires |companies| >= 1
  requires forall i :: 0 <= i < |companies| ==> |companies[i]| >= 1
  requires forall i, j :: 0 <= i < |companies| && 0 <= j < |companies[i]| ==> globalMax >= companies[i][j]
  ensures SumOverCompanies(companies, globalMax) == result : int
  decreases companies
{
  if |companies| == 1 {
    var companyMax := MaxInSeqFunc(companies[0]);
    assert globalMax >= companyMax;
  } else {
    var companyMax := MaxInSeqFunc(companies[0]);
    assert globalMax >= companyMax;
    SumOverCompaniesCorrect(companies[1..], globalMax);
  }
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
  var globalMax := GlobalMaxSalary(companies);
  GlobalMaxSalaryLemma(companies);
  CompanyMaxLemma(companies, globalMax);
  SumOverCompaniesNonNegative(companies, globalMax);
  result := SumOverCompanies(companies, globalMax);
}
// </vc-code>

