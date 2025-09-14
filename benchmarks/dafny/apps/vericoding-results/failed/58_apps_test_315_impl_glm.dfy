function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

// <vc-helpers>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

function CalcAdditionalWalks(a: seq<int>, finalSchedule: seq<int>): int
{
    sum(finalSchedule) - sum(a)
}

function ScheduleValue(s: seq<int>, i: int): int
{
    s[i]
}

function MinValue(x: int, y: int): int
{
    if x < y then x else y
}

lemma LemmaSumProperties(s: seq<int>)
    requires forall j :: 0 <= j < |s| ==> s[j] >= 0
    ensures sum(s) >= 0
    decreases |s|
{
    if |s| > 0 {
        LemmaSumProperties(s[1..]);
        assert sum(s) == s[0] + sum(s[1..]);
        assert s[0] >= 0 by (requirement forall j :: 0 <= j < |s| ==> s[j] >= 0; assert s[0] >= 0);
        assert sum(s[1..]) >= 0 by (LemmaSumProperties(s[1..]));
        assert sum(s) >= 0 + sum(s[1..]);
        assert sum(s) >= 0;
    }
}

lemma LemmaSequenceAgreement(s1: seq<int>, s2: seq<int>, i: int)
    requires 0 <= i < |s1|
    requires |s1| == |s2|
    requires forall j :: 0 <= j < |s1| ==> s1[j] == s2[j]
    ensures s1[i] == s2[i]
{
}

lemma LemmaValidOutputMaintained(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int, i: int)
    requires ValidInput(|a|, k, a) 
    requires |finalSchedule| == |a|
    requires forall j :: 0 <= j < |a| ==> finalSchedule[j] >= a[j]
    requires forall j :: 0 <= j < i - 1 ==> j < |a| - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k
    requires forall j :: i <= j < |a| ==> finalSchedule[j] == a[j]
    requires additionalWalks == CalcAdditionalWalks(a, finalSchedule)
    requires i < |a|
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
    decreases |a| - i
{
    if i == |a| - 1 {
        assert forall j :: 0 <= j < |a| ==> finalSchedule[j] >= a[j];
        assert forall j :: 0 <= j < |a| - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k;
        LemmaSumProperties(a);
        LemmaSumProperties(finalSchedule);
        assert additionalWalks >= 0;
    } else {
        calc {
            finalSchedule[i] + finalSchedule[i+1];
            >= // By requirement finalSchedule[i+1] == a[i+1]
            finalSchedule[i] + a[i+1];
        }
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

function CalcAdditionalWalks(a: seq<int>, finalSchedule: seq<int>): int
{
    sum(finalSchedule) - sum(a)
}

function ScheduleValue(s: seq<int>, i: int): int
{
    s[i]
}

function MinValue(x: int, y: int): int
{
    if x < y then x else y
}

lemma LemmaSumProperties(s: seq<int>)
    requires forall j :: 0 <= j < |s| ==> s[j] >= 0
    ensures sum(s) >= 0
    decreases |s|
{
    if |s| > 0 {
        LemmaSumProperties(s[1..]);
        assert sum(s) == s[0] + sum(s[1..]);
        assert s[0] >= 0 by (requirement forall j :: 0 <= j < |s| ==> s[j] >= 0; assert s[0] >= 0);
        assert sum(s[1..]) >= 0 by (LemmaSumProperties(s[1..]));
        assert sum(s) >= 0 + sum(s[1..]);
        assert sum(s) >= 0;
    }
}

lemma LemmaSequenceAgreement(s1: seq<int>, s2: seq<int>, i: int)
    requires 0 <= i < |s1|
    requires |s1| == |s2|
    requires forall j :: 0 <= j < |s1| ==> s1[j] == s2[j]
    ensures s1[i] == s2[i]
{
}

lemma LemmaValidOutputMaintained(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int, i: int)
    requires ValidInput(|a|, k, a) 
    requires |finalSchedule| == |a|
    requires forall j :: 0 <= j < |a| ==> finalSchedule[j] >= a[j]
    requires forall j :: 0 <= j < i - 1 ==> j < |a| - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k
    requires forall j :: i <= j < |a| ==> finalSchedule[j] == a[j]
    requires additionalWalks == CalcAdditionalWalks(a, finalSchedule)
    requires i < |a|
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
    decreases |a| - i
{
    if i == |a| - 1 {
        assert forall j :: 0 <= j < |a| ==> finalSchedule[j] >= a[j];
        assert forall j :: 0 <= j < |a| - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k;
        LemmaSumProperties(a);
        LemmaSumProperties(finalSchedule);
        assert additionalWalks >= 0;
    } else {
        calc {
            finalSchedule[i] + finalSchedule[i+1];
            >= // By requirement finalSchedule[i+1] == a[i+1]
            finalSchedule[i] + a[i+1];
        }
// </vc-code>

