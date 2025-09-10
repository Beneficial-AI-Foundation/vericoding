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
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) && (|combo| > |temp| ==> combo[|temp|] < i) ==> combo in result
    {
        var newTemp := temp + [i];
        sumAppend(temp, i);
        
        if sum(newTemp) <= n {
            ghost var extCombo: seq<int>;
            if |temp| < |fullCombo| && fullCombo[|temp|] == i {
                extCombo := fullCombo;
            } else {
                // Create a valid extension for the recursive call
                var remaining := k - |newTemp|;
                var needed := n - sum(newTemp);
                extCombo := newTemp;
                var nextVal := i + 1;
                while |extCombo| < k && nextVal <= 9
                    invariant |newTemp| <= |extCombo| <= k
                    invariant forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j]
                    invariant forall j :: |newTemp| <= j < |extCombo| ==> extCombo[j] >= i + 1
                    invariant forall j :: 0 <= j < |extCombo| - 1 ==> extCombo[j] < extCombo[j + 1]
                    invariant isDistinct(extCombo)
                    invariant forall j :: 0 <= j < |extCombo| ==> 1 <= extCombo[j] <= 9
                    invariant nextVal == (if |extCombo| == |newTemp| then i + 1 else extCombo[|extCombo| - 1] + 1)
                {
                    extCombo := extCombo + [nextVal];
                    nextVal := nextVal + 1;
                }
                
                // Ensure we have exactly k elements
                while |extCombo| < k
                    invariant |newTemp| <= |extCombo| <= k
                    invariant forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j]
                    invariant forall j :: |newTemp| <= j < |extCombo| ==> extCombo[j] >= i + 1
                    invariant forall j :: 0 <= j < |extCombo| - 1 ==> extCombo[j] < extCombo[j + 1]
                    invariant isDistinct(extCombo)
                    invariant forall j :: 0 <= j < |extCombo| ==> 1 <= extCombo[j] <= 9
                {
                    var lastVal := if |extCombo| == |newTemp| then i + 1 else extCombo[|extCombo| - 1] + 1;
                    if lastVal <= 9 {
                        extCombo := extCombo + [lastVal];
                    } else {
                        // Fill with smallest valid values
                        extCombo := extCombo + [9];
                    }
                }
                
                // Adjust sum to match n exactly
                var currentSum := sum(extCombo);
                if currentSum < n {
                    var diff := n - currentSum;
                    if |extCombo| > |newTemp| && extCombo[|extCombo| - 1] + diff <= 9 {
                        extCombo := extCombo[..|extCombo| - 1] + [extCombo[|extCombo| - 1] + diff];
                    }
                } else if currentSum > n && |extCombo| > |newTemp| {
                    var diff := currentSum - n;
                    if extCombo[|extCombo| - 1] - diff >= (if |extCombo| > |newTemp| + 1 then extCombo[|extCombo| - 2] + 1 else i + 1) {
                        extCombo := extCombo[..|extCombo| - 1] + [extCombo[|extCombo| - 1] - diff];
                    }
                }
            }
            
            assert |extCombo| == k;
            assert forall j :: 0 <= j < |newTemp| ==> extCombo[j] == newTemp[j];
            assert forall j :: |newTemp| <= j < |extCombo| ==> extCombo[j] >= i + 1;
            
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
    ghost var dummyCombo: seq<int> := [];
    ghost var j := 1;
    ghost var totalSum := 0;
    
    // Build a valid dummy combination
    while j <= 9 && |dummyCombo| < k
        invariant 1 <= j <= 10
        invariant 0 <= |dummyCombo| <= k
        invariant forall i :: 0 <= i < |dummyCombo| ==> 1 <= dummyCombo[i] <= 9
        invariant forall i :: 0 <= i < |dummyCombo| - 1 ==> dummyCombo[i] < dummyCombo[i + 1]
        invariant isDistinct(dummyCombo)
        invariant totalSum == sum(dummyCombo)
        invariant forall i :: 0 <= i < |dummyCombo| ==> dummyCombo[i] < j
    {
        dummyCombo := dummyCombo + [j];
        sumAppend(dummyCombo[..|dummyCombo| - 1], j);
        totalSum := totalSum + j;
        j := j + 1;
    }
    
    // Ensure we have exactly k elements
    while |dummyCombo| < k
        invariant 0 <= |dummyCombo| <= k
        invariant forall i :: 0 <= i < |dummyCombo| ==> 1 <= dummyCombo[i] <= 9
        invariant |dummyCombo| > 0 ==> forall i :: 0 <= i < |dummyCombo| - 1 ==> dummyCombo[i] < dummyCombo[i + 1]
        invariant isDistinct(dummyCombo)
        invariant totalSum == sum(dummyCombo)
    {
        var nextVal := if |dummyCombo| == 0 then 1 else if dummyCombo[|dummyCombo| - 1] < 9 then dummyCombo[|dummyCombo| - 1] + 1 else 9;
        dummyCombo := dummyCombo + [nextVal];
        sumAppend(dummyCombo[..|dummyCombo| - 1], nextVal);
        totalSum := totalSum + nextVal;
    }
    
    // Adjust the last element to make sum equal to n
    if totalSum != n && |dummyCombo| > 0 {
        var lastIdx := |dummyCombo| - 1;
        var diff := n - (totalSum - dummyCombo[lastIdx]);
        if 1 <= diff <= 9 && (lastIdx == 0 || dummyCombo[lastIdx - 1] < diff) {
            dummyCombo := dummyCombo[..lastIdx] + [diff];
        }
    }
    
    result := backtrack(k, n, 1, [], dummyCombo);
}
// </vc-code>

