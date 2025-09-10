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
lemma sumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        calc {
            sum(s + [x]);
            == (s + [x])[0] + sum((s + [x])[1..]);
            == s[0] + sum(s[1..] + [x]);
            == { sumAppend(s[1..], x); }
            s[0] + sum(s[1..]) + x;
            == sum(s) + x;
        }
    }
}

method backtrack(k: int, n: int, start: int, temp: seq<int>, ghost fullCombo: seq<int>) 
    returns (result: seq<seq<int>>)
    requires 1 <= start <= 10
    requires 0 <= |temp| <= k <= 9
    requires sum(temp) <= n
    requires forall i :: 0 <= i < |temp| ==> 1 <= temp[i] <= 9
    requires forall i :: 0 <= i < |temp| - 1 ==> temp[i] < temp[i + 1]
    requires |temp| > 0 ==> temp[|temp| - 1] < start
    requires isDistinct(temp)
    requires isValidExtension(temp, fullCombo, k, n, start)
    ensures forall i :: 0 <= i < |result| ==> isValidCombination(result[i], k, n)
    ensures forall i :: 0 <= i < |result| ==> |result[i]| >= |temp|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |temp| ==> result[i][j] == temp[j]
    ensures forall i :: 0 <= i < |result| ==> forall j :: |temp| <= j < |result[i]| ==> result[i][j] >= start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in result
    decreases 10 - start, k - |temp|
{
    result := [];
    
    if |temp| == k {
        if sum(temp) == n {
            result := [temp];
        }
        return;
    }
    
    var i := start;
    while i <= 9
        invariant start <= i <= 10
        invariant forall j :: 0 <= j < |result| ==> isValidCombination(result[j], k, n)
        invariant forall j :: 0 <= j < |result| ==> |result[j]| >= |temp|
        invariant forall j :: 0 <= j < |result| ==> forall l :: 0 <= l < |temp| ==> result[j][l] == temp[l]
        invariant forall j :: 0 <= j < |result| ==> forall l :: |temp| <= l < |result[j]| ==> result[j][l] >= start && result[j][l] < i
        invariant forall j, l :: 0 <= j < l < |result| ==> result[j] != result[l]
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) && (forall j :: |temp| <= j < |combo| ==> combo[j] < i) ==> combo in result
    {
        var newTemp := temp + [i];
        sumAppend(temp, i);
        
        if sum(newTemp) <= n {
            ghost var extCombo := if isValidExtension(temp, fullCombo, k, n, start) && 
                                     |fullCombo| > |temp| && fullCombo[|temp|] == i 
                                  then fullCombo else newTemp;
            
            var subResult := backtrack(k, n, i + 1, newTemp, extCombo);
            
            var j := 0;
            while j < |subResult|
                invariant 0 <= j <= |subResult|
                invariant forall l :: 0 <= l < |result| ==> isValidCombination(result[l], k, n)
                invariant forall l :: 0 <= l < |result| ==> |result[l]| >= |temp|
                invariant forall l :: 0 <= l < |result| ==> forall m :: 0 <= m < |temp| ==> result[l][m] == temp[m]
                invariant forall l, m :: 0 <= l < m < |result| ==> result[l] != result[m]
                invariant forall l :: 0 <= l < j ==> subResult[l] in result
            {
                if subResult[j] !in result {
                    result := result + [subResult[j]];
                }
                j := j + 1;
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
    result := backtrack(k, n, 1, [], []);
}
// </vc-code>

