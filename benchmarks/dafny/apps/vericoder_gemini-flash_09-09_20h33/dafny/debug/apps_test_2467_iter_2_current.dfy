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
method FindCombinations(
    k: int,
    n: int,
    start: int,
    temp: seq<int>,
    ghost result: set<seq<int>>
) returns (newResult: set<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    requires 1 <= start <= 9
    requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
    requires forall j :: 0 <= j < |temp| - 1 ==> temp[j] < temp[j+1]
    requires (forall j :: 0 <= j < |temp| ==> temp[j] < start) || |temp| == 0
    requires sum(temp) <= n
    requires |temp| <= k

    ensures forall combo :: isValidCombination(combo, k, n) && isValidExtension(temp, combo, k, n, start) ==> combo in newResult
    ensures forall combo :: combo in newResult ==> isValidCombination(combo, k, n) && isValidExtension(temp, combo, k, n, start)
    ensures forall c :: c in result ==> c in newResult

    decreases k - |temp|, n - sum(temp), 10 - start
{
    newResult := result; // Initialize newResult with the ghost variable result

    if k == |temp| {
        if n == sum(temp) {
            if isValidCombination(temp, k, n) {
                newResult := newResult + {temp}; // Add valid combination
            }
        }
        return newResult;
    }

    if start > 9 || n < sum(temp) {
        return newResult;
    }

    if k - |temp| > (9 - start + 1) { // Optimization: not enough remaining numbers
        return newResult;
    }
    if n - sum(temp) < ((k - |temp|) * (1 + 2)) / 2  // This is (k-|temp|) * (smallest possible sum)
     || n - sum(temp) > ((k - |temp|) * (9 + 8)) / 2 { // This is (k-|temp|) * (largest possible sum)
         return newResult;
     }

    // Case 1: Include 'start'
    var resultWithStart: set<seq<int>> := FindCombinations(k, n, start + 1, temp + [start], newResult);
    newResult := resultWithStart;

    // Case 2: Exclude 'start'
    var resultWithoutStart: set<seq<int>> := FindCombinations(k, n, start + 1, temp, newResult);

    // Merge results, avoiding duplicates
    newResult := newResult + resultWithoutStart;

    return newResult;
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
    var temp: seq<int> := [];
    var result_set := FindCombinations(k, n, 1, temp, {});
    var finalResult: seq<seq<int>> := [];

    // Convert set to sequence to match the return type
    for combo in result_set {
        finalResult := finalResult + [combo];
    }
    result := finalResult;
    return result;
}
// </vc-code>

