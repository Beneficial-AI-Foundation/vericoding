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
lemma StringToIntHelper_nonneg(s: string, pos: int)
  requires 0 <= pos <= |s|
  requires forall i :: 0 <= i < pos ==> '0' <= s[i] <= '9'
  ensures StringToIntHelper(s, pos) >= 0
  decreases pos
{
  if pos == 0 {
  } else {
    StringToIntHelper_nonneg(s, pos - 1);
    assert (s[pos - 1] as int - '0' as int) >= 0;
    // StringToIntHelper(s, pos) = StringToIntHelper(s, pos-1) * 10 + digit >= 0
  }
}

lemma StringToIntNonneg(s: string)
  requires IsValidIntegerString(s)
  ensures StringToInt(s) >= 0
{
  StringToIntHelper_nonneg(s, |s|);
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
  StringToIntNonneg(lines[0]);
  assert t >= 0;
  var a := new int[t];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant forall k :: 0 <= k < i ==> a[k] == MinDeletionsNeeded(lines[2 + 2*k])
  {
    a[i] := MinDeletionsNeeded(lines[2 + 2*i]);
    i := i + 1;
  }
  results := a[..];
}
// </vc-code>

