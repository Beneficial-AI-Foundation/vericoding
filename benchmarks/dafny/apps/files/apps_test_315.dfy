Given n consecutive days and a minimum requirement k, find the minimum additional walks needed
so that for any two consecutive days, the total walks is at least k. Can only increase walks.

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

lemma lemmaUpdateSum(prefix: seq<int>, oldVal: int, diff: int, suffix: seq<int>)
    ensures sum(prefix + [oldVal + diff] + suffix) == sum(prefix + [oldVal] + suffix) + diff
{
    if |prefix| == 0 {
        assert sum([oldVal + diff] + suffix) == (oldVal + diff) + sum(suffix);
        assert sum([oldVal] + suffix) == oldVal + sum(suffix);
    } else {
        assert prefix + [oldVal + diff] + suffix == [prefix[0]] + (prefix[1..] + [oldVal + diff] + suffix);
        assert prefix + [oldVal] + suffix == [prefix[0]] + (prefix[1..] + [oldVal] + suffix);
        lemmaUpdateSum(prefix[1..], oldVal, diff, suffix);
        assert sum(prefix[1..] + [oldVal + diff] + suffix) == sum(prefix[1..] + [oldVal] + suffix) + diff;
        assert sum(prefix + [oldVal + diff] + suffix) == prefix[0] + sum(prefix[1..] + [oldVal + diff] + suffix);
        assert sum(prefix + [oldVal] + suffix) == prefix[0] + sum(prefix[1..] + [oldVal] + suffix);
    }
}

method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
{
    var schedule := a;
    var ans := 0;

    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant |schedule| == n
        invariant ans >= 0
        invariant forall j :: 0 <= j < n ==> schedule[j] >= a[j]
        invariant forall j :: 0 <= j < i - 1 ==> schedule[j] + schedule[j + 1] >= k
        invariant ans == sum(schedule) - sum(a)
    {
        var diff := k - (schedule[i] + schedule[i - 1]);
        if diff > 0 {
            var oldSum := sum(schedule);
            var oldVal := schedule[i];
            var oldPrefix := schedule[..i];
            var oldSuffix := schedule[i+1..];
            assert schedule == oldPrefix + [oldVal] + oldSuffix;
            assert sum(schedule) == sum(oldPrefix + [oldVal] + oldSuffix);
            schedule := schedule[i := schedule[i] + diff];
            lemmaUpdateSum(oldPrefix, oldVal, diff, oldSuffix);
            assert schedule == oldPrefix + [oldVal + diff] + oldSuffix;
            assert sum(schedule) == sum(oldPrefix + [oldVal] + oldSuffix) + diff;
            assert sum(schedule) == oldSum + diff;
            ans := ans + diff;
        }
        i := i + 1;
    }

    additionalWalks := ans;
    finalSchedule := schedule;
}
