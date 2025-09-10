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
    // Optimization to check if sum is possible
    // Smallest possible sum for remaining k-|temp| numbers starting from 'start'
    var minRemainingSum: int := 0;
    var i: int := 0;
    while i < k - |temp|
        invariant 0 <= i <= k - |temp|
        invariant minRemainingSum == (i * (2 * start + i - 1)) / 2  // Sum of arithmetic progression start to start+i-1
    {
        minRemainingSum := minRemainingSum + start + i;
        i := i + 1;
    }
    // Largest possible sum for remaining k-|temp| numbers ending at 9
    var maxRemainingSum: int := 0;
    var j: int := 0;
    while j < k - |temp|
        invariant 0 <= j <= k - |temp|
        invariant maxRemainingSum == (j * (2 * 9 - j + 1)) / 2 // Sum of arithmetic progression 9, 8, ...
    {
        maxRemainingSum := maxRemainingSum + (9 - j);
        j := j + 1;
    }
    
    if n - sum(temp) < minRemainingSum || n - sum(temp) > maxRemainingSum {
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
    for combo' in result_set {
        finalResult := finalResult + [combo'];
    }
    result := finalResult;
    return result;
}
// </vc-code>

