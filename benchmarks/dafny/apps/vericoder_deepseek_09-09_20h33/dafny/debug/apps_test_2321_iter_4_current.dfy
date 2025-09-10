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
function GetTestcaseCount(t: string): int
    requires IsValidIntegerString(t)
    ensures GetTestcaseCount(t) == StringToInt(t)
{
    StringToInt(t)
}

lemma TestcaseIndexValid(lines: seq<string>, tcIndex: int)
    requires |lines| > 0
    requires IsValidIntegerString(lines[0])
    requires var t := GetTestcaseCount(lines[0]); 0 <= tcIndex < t
    ensures 1 + 2*tcIndex < |lines|
    ensures 2 + 2*tcIndex < |lines|
{
    var t := GetTestcaseCount(lines[0]);
    assert |lines| >= 1 + 2 * t;
    assert tcIndex < t;
    assert 2 + 2*tcIndex <= 2 + 2*(t-1);
    assert 2 + 2*(t-1) == 2*t;
    assert 2*t < 2*t + 1;
}

function ComputeMinDeletions(s: string): int
    requires IsValidProblemString(s)
    ensures ComputeMinDeletions(s) == MinDeletionsNeeded(s)
{
    var deleteFromLeft := FirstGreaterFromLeftHelper(s, 0);
    var deleteFromRight := FirstLessFromRightHelper(s, |s| - 1);
    if deleteFromLeft < deleteFromRight then deleteFromLeft else deleteFromRight
}

lemma FirstGreaterCorrect(s: string, pos: int)
    requires IsValidProblemString(s)
    requires 0 <= pos <= |s|
    ensures FirstGreaterFromLeftHelper(s, pos) >= pos
    decreases |s| - pos
{
    if pos < |s| {
        if s[pos] == '>' {
        } else {
            FirstGreaterCorrect(s, pos + 1);
        }
    }
}

lemma FirstLessCorrect(s: string, pos: int)
    requires IsValidProblemString(s)
    requires -1 <= pos < |s|
    ensures FirstLessFromRightHelper(s, pos) >= 0 && FirstLessFromRightHelper(s, pos) <= |s|
    decreases pos + 1
{
    if pos >= 0 {
        if s[pos] == '<' {
        } else {
            FirstLessCorrect(s, pos - 1);
        }
    }
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
    var testCaseCount := StringToInt(lines[0]);
    results := [];
    var index := 0;
    
    while index < testCaseCount
        invariant |results| == index
        invariant index <= testCaseCount
        invariant forall r :: r in results ==> r >= 0
        invariant forall i :: 0 <= i < |results| ==> 
            results[i] == MinDeletionsNeeded(lines[2 + 2*i])
    {
        TestcaseIndexValid(lines, index);
        assert 2 + 2*index < |lines|;
        var s := lines[2 + 2*index];
        var deletions := ComputeMinDeletions(s);
        results := results + [deletions];
        index := index + 1;
    }
}
// </vc-code>

