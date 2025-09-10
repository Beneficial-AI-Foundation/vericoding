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

method BuildCombinations(k: int, n: int, start: int, temp: seq<int>) returns (res: seq<seq<int>>)
requires k > 0 && n > 0 && k <= 9
requires 1 <= start <= 10
requires (temp == [] && start == 1) || (temp != [] && start == temp[|temp|-1] + 1)
requires |temp| <= k
requires sum(temp) <= n
requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
requires isDistinct(temp)
requires isSorted(temp)
requires if |temp| == k then sum(temp) == n
ensures forall i :: 0 <= i < |res| ==> isValidCombination(res[i], k, n)
ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
ensures forall combo :: isValidCombination(combo, k, n) && isValidExtension(temp, combo, k, n, start) ==> combo in res
ensures forall i :: 0 <= i < |res| ==> isValidExtension(temp, res[i], k, n, start)
decreases k - |temp|
{
   if |temp| == k {
      res := [temp];
   } else {
      res := [];
      var current := start;
      while current <= 9
         decreases 9 - current
      {
         if sum(temp) + current <= n { // Implied since recursive requires will check
            var new_temp := temp + [current];
            var sub_combos := BuildCombinations(k, n, current + 1, new_temp);
            res := res + sub_combos;
         }
         current := current + 1;
      }
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
   var result := BuildCombinations(k, n, 1, []);
   return result;
}
// </vc-code>

