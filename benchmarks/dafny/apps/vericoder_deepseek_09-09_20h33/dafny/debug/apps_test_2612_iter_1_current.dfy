predicate is_valid_beautiful_arrangement(arrangement: seq<int>, sizes: seq<int>)
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
{
    |arrangement| >= 1 &&
    // All indices are distinct
    (forall i, j :: 0 <= i < j < |arrangement| ==> arrangement[i] != arrangement[j]) &&
    // Indices are in increasing order
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    // Adjacent elements satisfy divisibility constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    // Adjacent elements satisfy size constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

predicate ValidInput(n: int, sizes: seq<int>)
{
    n >= 1 && |sizes| == n && forall i :: 0 <= i < n ==> sizes[i] >= 1
}

// <vc-helpers>
lemma MaxArrangementExists(n: int, sizes: seq<int>)
    requires ValidInput(n, sizes)
    ensures exists arrangement :: |arrangement| >= 1 && (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= n) && is_valid_beautiful_arrangement(arrangement, sizes)
{
    // At least the singleton arrangement exists
    var singleton := [1];
    assert is_valid_beautiful_arrangement(singleton, sizes);
}

lemma LemmaDivisibilityTransitive(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    requires b % a == 0 && c % b == 0
    ensures c % a == 0
{
}

lemma LemmaLTSizesTransitive(a: int, b: int, c: int, sizes: seq<int>)
    requires 1 <= a <= |sizes| && 1 <= b <= |sizes| && 1 <= c <= |sizes|
    requires sizes[a-1] < sizes[b-1] && sizes[b-1] < sizes[c-1]
    ensures sizes[a-1] < sizes[c-1]
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sizes: seq<int>) returns (result: int)
    requires ValidInput(n, sizes)
    ensures 1 <= result <= n
    ensures forall arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) ==> |arrangement| <= result
    ensures exists arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) && |arrangement| == result
// </vc-spec>
// <vc-code>
{
    var maxLength := 1;
    var dp := new int[n];
    
    // Initialize dp array with 1 (each element forms a beautiful arrangement of length 1)
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> dp[j] == 1
    {
        dp[i] := 1;
        i := i + 1;
    }
    
    // Dynamic programming: for each position, find the longest beautiful arrangement ending at that position
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < n ==> dp[j] >= 1
        invariant forall j :: 0 <= j < i ==> dp[j] <= maxLength
        invariant maxLength >= 1
    {
        if dp[i] > maxLength {
            maxLength := dp[i];
        }
        
        var j := i + 1;
        while j < n
            invariant i + 1 <= j <= n
            invariant forall k :: i < k < j ==> 
                dp[k] >= 1 && (if (k+1) % (i+1) == 0 && sizes[k] > sizes[i] && dp[i] + 1 > dp[k] 
                               then dp[k] == dp[i] + 1 else dp[k] == old(dp[k]))
        {
            // Check if j+1 is divisible by i+1 and sizes[j] > sizes[i]
            if (j+1) % (i+1) == 0 && sizes[j] > sizes[i] {
                if dp[i] + 1 > dp[j] {
                    dp[j] := dp[i] + 1;
                    if dp[j] > maxLength {
                        maxLength := dp[j];
                    }
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := maxLength;
}
// </vc-code>

