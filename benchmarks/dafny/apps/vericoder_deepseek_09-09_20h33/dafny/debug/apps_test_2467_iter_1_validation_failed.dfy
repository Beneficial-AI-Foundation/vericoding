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
lemma {:vcs_split_on_every_assert} LemmaSumNonNeg(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 9
  ensures sum(s) >= 0
{
}

lemma LemmaSumBounds(s: seq<int>, k: int)
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 9
  ensures |s| == k ==> k <= sum(s) <= 9*k
{
}

lemma LemmaMinimumSum(k: int) returns (minSum: int)
  requires 1 <= k <= 9
  ensures minSum == k*(k+1)/2
{
  if k == 1 {
    minSum := 1;
  } else {
    var prev := LemmaMinimumSum(k-1);
    minSum := prev + k;
  }
}

lemma LemmaMaximumSum(k: int) returns (maxSum: int)
  requires 1 <= k <= 9
  ensures maxSum == 9*k - (k*(k-1))/2
{
  if k == 1 {
    maxSum := 9;
  } else {
    var prev := LemmaMaximumSum(k-1);
    maxSum := prev + (10 - k);
  }
}

lemma LemmaValidCombinationConstraint(k: int, n: int)
  requires k > 0 && n > 0 && k <= 9
  ensures n >= k*(k+1)/2 && n <= 9*k - (k*(k-1))/2
{
}

ghost function combinations(k: int, n: int): set<seq<int>>
  reads *
{
  set combo | isValidCombination(combo, k, n) 
}

lemma LemmaCombinationsExist(k: int, n: int)
  requires k > 0 && n > 0 && k <= 9
  requires n >= k*(k+1)/2 && n <= 9*k - (k*(k-1))/2
  ensures |combinations(k, n)| > 0
{
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
    result := [];
    var temp: seq<int> := [];
    backtrack(k, n, 1, temp, ref result);
}

method backtrack(k: int, n: int, start: int, temp: seq<int>, ref result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    requires start >= 1 && start <= 10
    requires |temp| <= k
    requires forall x :: x in temp ==> 1 <= x <= 9
    requires isDistinct(temp) && isSorted(temp)
    requires sum(temp) <= n
    modifies result
    ensures |result| == old(|result|) + |set combo | isValidExtension(temp, combo, k, n, start)| - |old(result)| {}|
    ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in result
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    if |temp| == k {
        if sum(temp) == n {
            if temp !in result {
                result := result + [temp];
            }
        }
        return;
    }
    
    if sum(temp) > n {
        return;
    }
    
    var i := start;
    while i <= 9
        invariant i >= start && i <= 10
        invariant forall j :: start <= j < i ==> 
            forall combo :: isValidExtension(temp + [j], combo, k, n, j+1) ==> combo in result
        invariant forall combo :: combo in result ==> isValidCombination(combo, k, n)
        invariant forall x, y :: 0 <= x < y < |result| ==> result[x] != result[y]
    {
        var newTemp := temp + [i];
        var newSum := sum(newTemp);
        
        if newSum <= n {
            backtrack(k, n, i+1, newTemp, ref result);
        }
        
        i := i + 1;
    }
}
// </vc-code>

