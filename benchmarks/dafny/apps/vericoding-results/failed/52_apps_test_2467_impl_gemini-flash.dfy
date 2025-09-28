// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `for` loop syntax to iterate directly over sequence elements, removing unnecessary brackets and `in` keyword usage and ensuring proper sequence concatenation for `subCombinations`. Also ensured that the helper function `GetCombinations` is defined as a method not a function */
method GetCombinations(k: int, n: int, start: int) returns (result: seq<seq<int>>)
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
    ensures forall combo :: combo in result ==> (forall i :: 0 <= i < |combo| ==> combo[i] >= start)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  {
    if k == 0 then
      if n == 0 then result := [[]]
      else result := [];
    else if k < 0 || n < 0 then
      result := [];
    else if start > 9 then
      result := [];
    else {
      var combinations: seq<seq<int>> := [];

      // Option 1: Include 'start' in the combination
      if n >= start {
        var subCombinations := GetCombinations(k - 1, n - start, start + 1);
        for subCombo' in subCombinations {
          combinations := combinations + [[start] + subCombo'];
        }
      }

      // Option 2: Exclude 'start' from the combination, try with 'start + 1'
      var otherCombinations := GetCombinations(k, n, start + 1);
      combinations := combinations + otherCombinations;

      result := combinations;
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
/* code modified by LLM (iteration 5): Call the helper method GetCombinations to retrieve all valid combinations, and assign its result to the `result` variable. */
{
  result := GetCombinations(k, n, 1);
}
// </vc-code>
