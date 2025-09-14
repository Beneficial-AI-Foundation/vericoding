predicate IsValidString(s: string)
{
    |s| > 0
}

predicate IsValidProblemString(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '>' || s[i] == '<'
}

predicate IsValidIntegerString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
    requires IsValidIntegerString(s)
{
    StringToIntHelper(s, |s|)
}

function StringToIntHelper(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < pos ==> '0' <= s[i] <= '9'
{
    if pos == 0 then 0
    else StringToIntHelper(s, pos - 1) * 10 + (s[pos - 1] as int - '0' as int)
}

function MinDeletionsNeeded(s: string): int
    requires IsValidProblemString(s)
{
    var firstGreater := FirstGreaterFromLeft(s);
    var firstLessFromRight := FirstLessFromRight(s);
    if firstGreater < firstLessFromRight then firstGreater else firstLessFromRight
}

function FirstGreaterFromLeft(s: string): int
    requires IsValidProblemString(s)
    ensures 0 <= FirstGreaterFromLeft(s) <= |s|
{
    FirstGreaterFromLeftHelper(s, 0)
}

function FirstGreaterFromLeftHelper(s: string, pos: int): int
    requires IsValidProblemString(s)
    requires 0 <= pos <= |s|
    ensures 0 <= FirstGreaterFromLeftHelper(s, pos) <= |s|
    decreases |s| - pos
{
    if pos >= |s| then |s|
    else if s[pos] == '>' then pos
    else FirstGreaterFromLeftHelper(s, pos + 1)
}

function FirstLessFromRight(s: string): int
    requires IsValidProblemString(s)
    ensures 0 <= FirstLessFromRight(s) <= |s|
{
    FirstLessFromRightHelper(s, |s| - 1)
}

function FirstLessFromRightHelper(s: string, pos: int): int
    requires IsValidProblemString(s)
    requires -1 <= pos < |s|
    ensures 0 <= FirstLessFromRightHelper(s, pos) <= |s|
    decreases pos + 1
{
    if pos < 0 then |s|
    else if s[pos] == '<' then |s| - 1 - pos
    else FirstLessFromRightHelper(s, pos - 1)
}

function min(a: int, b: int): int
{
    if a < b then a else b
}

// <vc-helpers>
lemma MinDelNonNeg(s: string)
    requires IsValidProblemString(s)
    ensures MinDeletionsNeeded(s) >= 0
{
    assert MinDeletionsNeeded(s) ==
        (if FirstGreaterFromLeft(s) < FirstLessFromRight(s)
         then FirstGreaterFromLeft(s)
         else FirstLessFromRight(s));

    if FirstGreaterFromLeft(s) < FirstLessFromRight(s) {
        assert 0 <= FirstGreaterFromLeft(s);
        assert MinDeletionsNeeded(s) == FirstGreaterFromLeft(s);
        assert 0 <= MinDeletionsNeeded(s);
    } else {
        assert 0 <= FirstLessFromRight(s);
        assert MinDeletionsNeeded(s) == FirstLessFromRight(s);
        assert 0 <= MinDeletionsNeeded(s);
    }
}

lemma StringToIntHelperNonNeg(s: string, pos: int)
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < pos ==> '0' <= s[i] <= '9'
    ensures StringToIntHelper(s, pos) >= 0
    decreases pos
{
    if pos == 0 {
        assert StringToIntHelper(s, pos) == 0;
    } else {
        StringToIntHelperNonNeg(s, pos - 1);
        assert 0 <= s[pos - 1] as int - '0' as int;
        assert StringToIntHelper(s, pos) ==
            StringToIntHelper(s, pos - 1) * 10 + (s[pos - 1] as int - '0' as int);
    }
}

lemma StringToIntNonNeg(s: string)
    requires IsValidIntegerString(s)
    ensures StringToInt(s) >= 0
{
    StringToIntHelperNonNeg(s, |s|);
}
// </vc-helpers>

// <vc-spec>
method solve(lines: seq<string>) returns (results: seq<int>)
    requires |lines| > 0
    requires forall i :: 0 <= i < |lines| ==> IsValidString(lines[i])
    requires IsValidIntegerString(lines[0])
    requires var t := StringToInt(lines[0]); |lines| >= 1 + 2 * t
    requires forall i :: 0 <= i < StringToInt(lines[0]) ==> 
        IsValidIntegerString(lines[1 + 2*i]) && IsValidProblemString(lines[2 + 2*i])
    ensures |results| == StringToInt(lines[0])
    ensures forall r :: r in results ==> r >= 0
    ensures forall i :: 0 <= i < |results| ==> 
        results[i] == MinDeletionsNeeded(lines[2 + 2*i])
// </vc-spec>
// <vc-code>
{
  var t := StringToInt(lines[0]);
  StringToIntNonNeg(lines[0]);
  assert t >= 0;
  var r: seq<int> := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == MinDeletionsNeeded(lines[2 + 2*j])
    invariant forall j :: 0 <= j < i ==> r[j] >= 0
  {
    assert 0 <= i < t;
    assert 2 + 2*i <= 2*t;
    assert 2*t < |lines|;
    assert 2 + 2*i < |lines|;
    assert IsValidProblemString(lines[2 + 2*i]);
    MinDelNonNeg(lines[2 + 2*i]);
    var v := MinDeletionsNeeded(lines[2 + 2*i]);
    assert v >= 0;
    r := r + [v];
    i := i + 1;
  }
  results := r;
  assert forall i :: 0 <= i < |results| ==> results[i] >= 0;
}
// </vc-code>

