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
            == { assert (s + [x])[1..] == s[1..] + [x]; }
            s[0] + sum(s[1..] + [x]);
            == { sumAppend(s[1..], x); }
            s[0] + sum(s[1..]) + x;
            == sum(s) + x;
        }
    }
}

lemma sumMonotonic(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures sum(s) >= |s|
{
    if |s| == 0 {
        assert sum(s) == 0;
    } else {
        sumMonotonic(s[1..]);
        assert sum(s) == s[0] + sum(s[1..]) >= 1 + |s[1..]| == |s|;
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
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) && (|combo| > |temp| && combo[|temp|] < i) ==> combo in result
    {
        var newTemp := temp + [i];
        sumAppend(temp, i);
        
        if sum(newTemp) <= n {
            ghost var extCombo: seq<int>;
            if |temp| < |fullCombo| && fullCombo[|temp|] == i {
                extCombo := fullCombo;
            } else {
                // Create a valid extension for the recursive call
                extCombo := newTemp;
                var nextVal := i + 1;
                var currentSum := sum(newTemp);
                
                while |extCombo| < k && nextVal <= 9
                    invariant |newTemp| <= |extCombo| <= k
                    invariant forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j]
                    invariant forall j :: |newTemp| <= j < |extCombo| ==> i + 1 <= extCombo[j] <= 9
                    invariant forall j :: 0 <= j < |extCombo| - 1 ==> extCombo[j] < extCombo[j + 1]
                    invariant forall j :: 0 <= j < |extCombo| ==> 1 <= extCombo[j] <= 9
                    invariant nextVal <= 10
                    invariant |extCombo| > |newTemp| ==> nextVal == extCombo[|extCombo| - 1] + 1
                    invariant |extCombo| == |newTemp| ==> nextVal == i + 1
                    invariant currentSum == sum(extCombo)
                {
                    extCombo := extCombo + [nextVal];
                    sumAppend(extCombo[..|extCombo|-1], nextVal);
                    currentSum := currentSum + nextVal;
                    nextVal := nextVal + 1;
                }
                
                // Fill remaining spots if needed
                while |extCombo| < k
                    invariant |newTemp| <= |extCombo| <= k
                    invariant forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j]
                    invariant forall j :: |newTemp| <= j < |extCombo| ==> i + 1 <= extCombo[j] <= 9
                    invariant forall j :: 0 <= j < |extCombo| - 1 ==> extCombo[j] < extCombo[j + 1]
                    invariant forall j :: 0 <= j < |extCombo| ==> 1 <= extCombo[j] <= 9
                    invariant currentSum == sum(extCombo)
                {
                    var lastVal := if |extCombo| > |newTemp| then extCombo[|extCombo| - 1] else i;
                    if lastVal < 9 {
                        extCombo := extCombo + [lastVal + 1];
                        sumAppend(extCombo[..|extCombo|-1], lastVal + 1);
                        currentSum := currentSum + lastVal + 1;
                    } else {
                        extCombo := extCombo + [9];
                        sumAppend(extCombo[..|extCombo|-1], 9);
                        currentSum := currentSum + 9;
                    }
                }
                
                // Adjust to get sum == n if possible
                if currentSum != n && |extCombo| == k {
                    var diff := n - currentSum;
                    if diff > 0 && |extCombo| > |newTemp| && extCombo[|extCombo| - 1] + diff <= 9 {
                        var oldLast := extCombo[|extCombo| - 1];
                        extCombo := extCombo[..|extCombo| - 1] + [oldLast + diff];
                    } else if diff < 0 && |extCombo| > |newTemp| {
                        var oldLast := extCombo[|extCombo| - 1];
                        var minVal := if |extCombo| > |newTemp| + 1 then extCombo[|extCombo| - 2] + 1 else i + 1;
                        if oldLast + diff >= minVal {
                            extCombo := extCombo[..|extCombo| - 1] + [oldLast + diff];
                        }
                    }
                }
            }
            
            assert |extCombo| == k;
            assert forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j];
            
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
    // Build a valid dummy combination with sum n
    ghost var dummyCombo: seq<int> := [];
    ghost var targetSum := n;
    ghost var remaining := k;
    ghost var nextVal := 1;
    
    // Try to build a valid combination
    while remaining > 0 && nextVal <= 9
        invariant 0 <= remaining <= k
        invariant |dummyCombo| == k - remaining
        invariant 1 <= nextVal <= 10
        invariant forall i :: 0 <= i < |dummyCombo| ==> 1 <= dummyCombo[i] <= 9
        invariant forall i :: 0 <= i < |dummyCombo| - 1 ==> dummyCombo[i] < dummyCombo[i + 1]
        invariant |dummyCombo| > 0 ==> dummyCombo[|dummyCombo| - 1] < nextVal
        invariant sum(dummyCombo) <= n
    {
        if remaining == 1 {
            // Last element - try to match exactly
            var needed := n - sum(dummyCombo);
            if nextVal <= needed && needed <= 9 {
                dummyCombo := dummyCombo + [needed];
                sumAppend(dummyCombo[..|dummyCombo|-1], needed);
                remaining := 0;
            } else {
                dummyCombo := dummyCombo + [nextVal];
                sumAppend(dummyCombo[..|dummyCombo|-1], nextVal);
                remaining := 0;
            }
        } else {
            dummyCombo := dummyCombo + [nextVal];
            sumAppend(dummyCombo[..|dummyCombo|-1], nextVal);
            remaining := remaining - 1;
            nextVal := nextVal + 1;
        }
    }
    
    // If we couldn't build k elements, fill with remaining values
    while |dummyCombo| < k
        invariant 0 <= |dummyCombo| <= k
        invariant forall i :: 0 <= i < |dummyCombo| ==> 1 <= dummyCombo[i] <= 9
        invariant forall i :: 0 <= i < |dummyCombo| - 1 ==> dummyCombo[i] < dummyCombo[i + 1]
    {
        var lastVal := if |dummyCombo| == 0 then 1 else dummyCombo[|dummyCombo| - 1];
        if lastVal < 9 {
            dummyCombo := dummyCombo + [lastVal + 1];
            sumAppend(dummyCombo[..|dummyCombo|-1], lastVal + 1);
        } else {
            dummyCombo := dummyCombo + [9];
            sumAppend(dummyCombo[..|dummyCombo|-1], 9);
        }
    }
    
    // Adjust to make sum exactly n if needed
    if sum(dummyCombo) != n && |dummyCombo| > 0 {
        var currentSum := sum(dummyCombo);
        var diff := n - currentSum;
        if diff > 0 && dummyCombo[|dummyCombo| - 1] + diff <= 9 {
            var oldLast := dummyCombo[|dummyCombo| - 1];
            dummyCombo := dummyCombo[..|dummyCombo| - 1] + [oldLast + diff];
        } else if diff < 0 {
            var idx := |dummyCombo| - 1;
            while idx >= 0 && diff < 0
                invariant -1 <= idx < |dummyCombo|
                invariant sum(dummyCombo) - n == -diff
            {
                var reduction := if -diff < dummyCombo[idx] - 1 then -diff else dummyCombo[idx] - 1;
                if reduction > 0 && (idx == 0 || dummyCombo[idx] - reduction > dummyCombo[idx - 1]) {
                    dummyCombo := dummyCombo[..idx] + [dummyCombo[idx] - reduction] + dummyCombo[idx+1..];
                    diff := diff + reduction;
                }
                idx := idx - 1;
            }
        }
    }
    
    assert |dummyCombo| == k;
    result := backtrack(k, n, 1, [], dummyCombo);
}
// </vc-code>

