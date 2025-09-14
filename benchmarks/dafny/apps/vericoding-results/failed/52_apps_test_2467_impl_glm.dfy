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

// <vc-helpers>
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

method findCombinations(k: int, n: int, start: int, temp: seq<int>) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9 && start <= 10
    requires 1 <= start <= 9
    requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
    requires isDistinct(temp) && isSorted(temp)
    ensures forall i :: 0 <= i < |result| ==> isValidCombination(result[i], k, n)
    ensures forall combo :: combo in result ==> isValidExtension(temp, combo, k, n, start)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    if k == 0 {
        if n == 0 {
            result := [temp];
        } else {
            result := [];
        }
    } else if start > 9 || n < 1 {
        result := [];
    } else {
        var rec_include := findCombinations(k - 1, n - start, start + 1, temp + [start]);
        var rec_exclude := findCombinations(k, n, start + 1, temp);
        result := rec_include + rec_exclude;
    }
}

lemma findAllCombinations(k: int, n: int)
    requires k > 0 && n > 0 && k <= 9
    ensures var allFound := findCombinations(k, n, 1, []);
           forall combo :: isValidCombination(combo, k, n) ==> combo in allFound
{
    if k == 0 {
    } else if n < 1 {
    } else {
        forall combo | isValidCombination(combo, k, n)
            ensures combo in findCombinations(k, n, 1, [])
        {
            if |combo| > 0 && combo[0] == 1 {
                var restCombo := combo[1..];
                assert isValidCombination(restCombo, k - 1, n - 1) by {
                    forall i, j | 0 <= i < j < |restCombo|
                        ensures restCombo[i] != restCombo[j]
                    {
                        assert combo[i + 1] != combo[j + 1];
                    }
                }
                findAllCombinations(k - 1, n - 1);
                assert restCombo in findCombinations(k - 1, n - 1, 2, []);
                assert combo in findCombinations(k, n, 1, []);
            } else if |combo| > 0 && combo[0] > 1 {
                findAllCombinations(k, n);
                assert combo in findCombinations(k, n, 2, []);
                assert combo in findCombinations(k, n, 1, []);
            }
        }
    }
}

lemma NoDuplicatesInGenerated(k: int, n: int)
    requires k > 0 && n > 0 && k <= 9
    ensures var result := findCombinations(k, n, 1, []);
           forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var result := findCombinations(k, n, 1, []);
    if k == 0 {
    } else if n < 1 {
    } else {
        assert forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j];
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    var temp := findCombinations(k, n, 1, []);
    findAllCombinations(k, n);
    NoDuplicatesInGenerated(k, n);
    result := temp;
}
// </vc-code>

