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
lemma MaxInSeq_le_if_all_le(s: seq<int>, m: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] <= m
  ensures MaxInSeq(s) <= m
  decreases |s|
{
  if |s| == 1 {
  } else {
    var tail := s[1..];
    MaxInSeq_le_if_all_le(tail, m);
    var mt := MaxInSeq(tail);
    if s[0] >= mt {
    } else {
    }
  }
}

lemma SumOverCompanies_monotone(companies: seq<seq<int>>, g1: int, g2: int)
  requires |companies| >= 1
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  requires forall k :: 0 <= k < |companies| ==> MaxInSeq(companies[k]) <= g2
  requires g1 >= g2
  ensures SumOverCompanies(companies, g1) >= SumOverCompanies(companies, g2)
  decreases |companies|
{
  if |companies| == 1 {
    var m := MaxInSeqFunc(companies[0]);
    var a := g1 - m;
    var b := g2 - m;
    assert a >= b;
    assert a * |companies[0]| >= b * |companies[0]|;
  } else {
    var m := MaxInSeqFunc(companies[0]);
    var a := g1 - m;
    var b := g2 - m;
    assert a >= b;
    assert a * |companies[0]| >= b * |companies[0]|;
    SumOverCompanies_monotone(companies[1..], g1, g2);
    assert SumOverCompanies(companies, g1) == a * |companies[0]| + SumOverCompanies(companies[1..], g1);
    assert SumOverCompanies(companies, g2) == b * |companies[0]| + SumOverCompanies(companies[1..], g2);
    assert a * |companies[0]| + SumOverCompanies(companies[1..], g1) >= b * |companies[0]| + SumOverCompanies(companies[1..], g2);
  }
}

lemma MaxInSeq_ge(s: seq<int>, idx: int)
  requires |s| > 0
  requires 0 <= idx < |s|
  ensures s[idx] <= MaxInSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    var tail := s[1..];
    if idx == 0 {
      var mt := MaxInSeq(tail);
      if s[0] >= mt {
      } else {
      }
    } else {
      MaxInSeq_ge(tail, idx - 1);
      var mt := MaxInSeq(tail);
      if s[0] >= mt {
      } else {
      }
    }
  }
}

lemma AllElements_le_Max(s: seq<int>)
  requires |s| > 0
  ensures forall idx :: 0 <= idx < |s| ==> s[idx] <= MaxInSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    var tail := s[1..];
    AllElements_le_Max(tail);
    var mt := MaxInSeq(tail);
    if s[0] >= mt {
    } else {
    }
  }
}

lemma MaxTail_le_Max(s: seq<int>)
  requires |s| >= 2
  ensures MaxInSeq(s[1..]) <= MaxInSeq(s)
  decreases |s|
{
  var tail := s[1..];
  if s[0] >= MaxInSeq(tail) {
  } else {
  }
}

lemma CompanyMax_le_Global(companies: seq<seq<int>>, idx: int)
  requires |companies| >= 1
  requires 0 <= idx < |companies|
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  ensures MaxInSeq(companies[idx]) <= GlobalMaxSalary(companies)
{
  var seqOfMax := seq(|companies|, k requires 0 <= k < |companies| && |companies[k]| >= 1 => MaxInSeqFunc(companies[k]));
  // seqOfMax has length |companies| and for each k its element is MaxInSeqFunc(companies[k])
  MaxInSeq_ge(seqOfMax, idx);
  assert seqOfMax[idx] == MaxInSeqFunc(companies[idx]);
  assert GlobalMaxSalary(companies) == MaxInSeqOfSeq(seqOfMax);
  assert seqOfMax[idx] <= GlobalMaxSalary(companies);
}

lemma CalculateMinimumIncrease_nonnegative(companies: seq<seq<int>>)
  requires |companies| >= 1
  requires forall k :: 0 <= k < |companies| ==> |companies[k]| >= 1
  ensures CalculateMinimumIncrease(companies) >= 0
  decreases |companies|
{
  var g := GlobalMaxSalary(companies);
  if |companies| == 1 {
    var m := MaxInSeqFunc(companies[0]);
    CompanyMax_le_Global(companies, 0);
    assert m <= g;
    assert g - m >= 0;
    assert (g - m) * |companies[0]| >= 0;
  } else {
    var m := MaxInSeqFunc(companies[0]);
    CompanyMax_le_Global(companies, 0);
    assert m <= g;
    var tail := companies[1..];
    CalculateMinimumIncrease_nonnegative(tail);
    var gTail := GlobalMaxSalary(tail);

    // Build seq of maxima for companies and for tail with explicit per-index preconditions
    var seqOfMax := seq(|companies|, k requires 0 <= k < |companies| && |companies[k]| >= 1 => MaxInSeqFunc(companies[k]));
    var seqTailOfMax := seq(|tail|, k requires 0 <= k < |tail| && |tail[k]| >= 1 => MaxInSeqFunc(tail[k]));

    // Relate globals to these sequences
    assert g == MaxInSeqOfSeq(seqOfMax);
    assert gTail == MaxInSeqOfSeq(seqTailOfMax);

    // show MaxInSeqOfSeq(seqTailOfMax) <= MaxInSeqOfSeq(seqOfMax)
    if |seqOfMax| >= 2 {
      MaxTail_le_Max(seqOfMax);
      assert MaxInSeqOfSeq(seqTailOfMax) <= MaxInSeqOfSeq(seqOfMax);
    } else {
      // if seqOfMax length is 1 then tail is empty, but this branch is in else so |companies|>1 hence seqOfMax has length >=2
    }

    assert g >= gTail;

    // For using SumOverCompanies_monotone we need that for all k in tail, MaxInSeq(tail[k]) <= gTail
    if |tail| > 0 {
      AllElements_le_Max(seqTailOfMax);
      assert forall k | 0 <= k < |tail| :: MaxInSeqFunc(tail[k]) <= gTail;
    }

    // From recursive call we have SumOverCompanies(tail, gTail) >= 0
    // Lift it to g using monotonicity
    SumOverCompanies_monotone(tail, g, gTail);

    assert (g - m) * |companies[0]| >= 0;
    assert SumOverCompanies(tail, g) >= 0;
  }

  assert CalculateMinimumIncrease(companies) == SumOverCompanies(companies, g);
  assert SumOverCompanies(companies, g) >= 0;
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

