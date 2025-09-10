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
lemma sumAppend(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        sumAppend(s1[1..], s2);
    }
}

lemma sumSingle(x: int)
    ensures sum([x]) == x
{
}

lemma isDistinctAppend(s: seq<int>, x: int)
    requires isDistinct(s)
    requires x !in s
    ensures isDistinct(s + [x])
{
}

lemma isSortedAppend(s: seq<int>, x: int)
    requires isSorted(s)
    requires |s| == 0 || s[|s|-1] < x
    ensures isSorted(s + [x])
{
}

lemma validExtensionToValidCombination(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int)
    requires |temp| == 0
    requires isValidExtension(temp, combo, k, n, start)
    ensures isValidCombination(combo, k, n)
{
}

lemma validCombinationToValidExtension(combo: seq<int>, k: int, n: int)
    requires isValidCombination(combo, k, n)
    ensures isValidExtension([], combo, k, n, 1)
{
}

method backtrack(temp: seq<int>, k: int, n: int, start: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9 && start >= 1
    requires |temp| <= k
    requires sum(temp) <= n
    requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
    requires isDistinct(temp)
    requires isSorted(temp)
    requires |temp| == 0 || temp[|temp|-1] < start
    decreases k - |temp|, 10 - start
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in result
    ensures forall combo :: combo in result ==> isValidExtension(temp, combo, k, n, start)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    if |temp| == k {
        if sum(temp) == n {
            result := [temp];
        } else {
            result := [];
        }
        return;
    }
    
    result := [];
    var i := start;
    while i <= 9
        invariant start <= i <= 10
        invariant forall combo :: combo in result ==> isValidExtension(temp, combo, k, n, start)
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) && (|combo| > |temp| ==> combo[|temp|] < i) ==> combo in result
        invariant forall x, y :: 0 <= x < y < |result| ==> result[x] != result[y]
    {
        if i !in temp && (|temp| == 0 || temp[|temp|-1] < i) {
            var newTemp := temp + [i];
            sumAppend(temp, [i]);
            sumSingle(i);
            
            if sum(newTemp) <= n {
                isDistinctAppend(temp, i);
                isSortedAppend(temp, i);
                
                var subResult := backtrack(newTemp, k, n, i + 1);
                
                // Prove distinctness before concatenation
                forall x, y | 0 <= x < |result| && 0 <= y < |subResult|
                    ensures result[x] != subResult[y]
                {
                    // Different extensions lead to different results
                }
                
                result := result + subResult;
            }
        }
        i := i + 1;
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
    var backtrackResult := backtrack([], k, n, 1);
    
    // Establish connection between isValidExtension and isValidCombination
    forall combo | combo in backtrackResult
        ensures isValidCombination(combo, k, n)
    {
        validExtensionToValidCombination([], combo, k, n, 1);
    }
    
    forall combo | isValidCombination(combo, k, n)
        ensures combo in backtrackResult
    {
        validCombinationToValidExtension(combo, k, n);
    }
    
    result := backtrackResult;
}
// </vc-code>

