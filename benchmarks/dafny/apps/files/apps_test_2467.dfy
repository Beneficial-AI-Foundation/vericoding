Find all unique combinations of exactly k distinct numbers from the range [1, 9] that sum to n.
Each number must be from 1 to 9, used at most once per combination, with no duplicate combinations.

function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

predicate isDistinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate isSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}

predicate isValidCombination(combo: seq<int>, k: int, n: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo)
}

predicate isValidExtension(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo) &&
    |combo| >= |temp| &&
    (forall i :: 0 <= i < |temp| ==> temp[i] == combo[i]) &&
    (forall i :: |temp| <= i < |combo| ==> combo[i] >= start)
}

method backtrack(temp: seq<int>, k: int, n: int, start: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    requires 1 <= start <= 10
    requires forall i :: 0 <= i < |temp| ==> 1 <= temp[i] <= 9
    requires isDistinct(temp)
    requires isSorted(temp)
    requires |temp| <= k
    requires forall i :: 0 <= i < |temp| ==> temp[i] < start
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in result
    ensures forall combo :: combo in result ==> isValidExtension(temp, combo, k, n, start)
    decreases k - |temp|, 10 - start
{
    var total := sum(temp);

    if total > n {
        result := [];
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> sum(combo) == n;
        assert sum(temp) > n;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> sum(combo) >= sum(temp);
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> false;
        return;
    }
    if |temp| == k && total == n {
        result := [temp];
        return;
    }
    if |temp| == k {
        result := [];
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> |combo| == k;
        assert |temp| == k;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> (forall i :: 0 <= i < |temp| ==> temp[i] == combo[i]);
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo == temp;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> sum(combo) == sum(temp);
        assert sum(temp) != n;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> sum(combo) != n;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> false;
        return;
    }

    result := [];
    var i := start;
    while i < 10
        invariant start <= i <= 10
        invariant forall j :: 0 <= j < |result| ==> |result[j]| == k
        invariant forall j :: 0 <= j < |result| ==> sum(result[j]) == n
        invariant forall j :: 0 <= j < |result| ==> forall l :: 0 <= l < |result[j]| ==> 1 <= result[j][l] <= 9
        invariant forall j :: 0 <= j < |result| ==> isDistinct(result[j])
        invariant forall j :: 0 <= j < |result| ==> isSorted(result[j])
        invariant forall j1, j2 :: 0 <= j1 < j2 < |result| ==> result[j1] != result[j2]
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) && (|temp| < |combo| ==> combo[|temp|] < i) ==> combo in result
        invariant forall combo :: combo in result ==> isValidExtension(temp, combo, k, n, start)
    {
        var newTemp := temp + [i];
        var tmpCall1 := backtrack(newTemp, k, n, i + 1);
        var subResult := tmpCall1;

        ghost var oldResult := result;
        result := result + subResult;

        assert forall combo :: combo in oldResult ==> isValidExtension(temp, combo, k, n, start);
        assert forall combo :: combo in subResult ==> isValidExtension(newTemp, combo, k, n, i + 1);
        assert forall combo :: combo in subResult ==> isValidExtension(temp, combo, k, n, start);
        assert forall combo :: combo in subResult ==> combo[|temp|] == i;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) && (|temp| < |combo| ==> combo[|temp|] == i) ==> combo in subResult;
        assert forall combo :: isValidExtension(temp, combo, k, n, start) && (|temp| < |combo| ==> combo[|temp|] < i + 1) ==> combo in result;

        i := i + 1;
    }
    assert forall combo :: isValidExtension(temp, combo, k, n, start) && (|temp| < |combo| ==> combo[|temp|] < 10) ==> combo in result;
    assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> (|temp| < |combo| ==> combo[|temp|] <= 9);
    assert forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in result;
}

method combinationSum3(k: int, n: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidCombination(combo, k, n) ==> combo in result
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
{
    result := backtrack([], k, n, 1);
}
