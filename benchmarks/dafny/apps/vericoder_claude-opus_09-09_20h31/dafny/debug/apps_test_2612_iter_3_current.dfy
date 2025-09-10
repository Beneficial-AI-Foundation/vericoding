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
lemma SingletonIsValid(i: int, sizes: seq<int>)
    requires 1 <= i <= |sizes|
    requires forall j :: 0 <= j < |sizes| ==> sizes[j] >= 1
    ensures is_valid_beautiful_arrangement([i], sizes)
{
    // A single element arrangement is always valid
}

lemma ExtendArrangement(arrangement: seq<int>, next: int, sizes: seq<int>)
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
    requires 1 <= next <= |sizes|
    requires is_valid_beautiful_arrangement(arrangement, sizes)
    requires arrangement[|arrangement| - 1] < next
    requires next % arrangement[|arrangement| - 1] == 0
    requires sizes[arrangement[|arrangement| - 1] - 1] < sizes[next - 1]
    requires forall i :: 0 <= i < |arrangement| ==> arrangement[i] != next
    ensures is_valid_beautiful_arrangement(arrangement + [next], sizes)
{
    var extended := arrangement + [next];
    
    // Verify all properties of valid arrangement
    assert |extended| >= 1;
    
    // All indices are distinct
    forall i, j | 0 <= i < j < |extended|
        ensures extended[i] != extended[j]
    {
        if j < |arrangement| {
            assert extended[i] == arrangement[i] && extended[j] == arrangement[j];
        } else {
            assert j == |arrangement| && extended[j] == next;
            if i < |arrangement| {
                assert extended[i] == arrangement[i];
                assert arrangement[i] != next;
            }
        }
    }
    
    // Indices are in increasing order
    forall i | 0 <= i < |extended| - 1
        ensures extended[i] < extended[i + 1]
    {
        if i < |arrangement| - 1 {
            assert extended[i] == arrangement[i] && extended[i + 1] == arrangement[i + 1];
        } else {
            assert i == |arrangement| - 1;
            assert extended[i] == arrangement[|arrangement| - 1];
            assert extended[i + 1] == next;
        }
    }
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
    // dp[i] will store the maximum length of valid arrangement ending at index i+1
    var dp := new int[n];
    var parent := new int[n];
    
    // Initialize: each index can start an arrangement of length 1
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant forall j :: 0 <= j < k ==> dp[j] == 1
        invariant forall j :: 0 <= j < k ==> parent[j] == -1
    {
        dp[k] := 1;
        parent[k] := -1;
        SingletonIsValid(k + 1, sizes);
        k := k + 1;
    }
    
    // For each position i, try to extend arrangements ending at previous positions
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < n ==> dp[j] >= 1
        invariant forall j :: 0 <= j < n ==> dp[j] <= n
        invariant forall j :: 0 <= j < i ==> dp[j] <= j + 1
        invariant forall j :: 0 <= j < n ==> parent[j] < j
        invariant forall j :: 0 <= j < n ==> parent[j] >= -1
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant dp[i] <= i + 1
            invariant parent[i] < i
            invariant parent[i] >= -1
        {
            // Check if we can extend arrangement ending at j to include i
            // Need: (i+1) % (j+1) == 0 and sizes[j] < sizes[i]
            if (i + 1) % (j + 1) == 0 && sizes[j] < sizes[i] {
                if dp[j] + 1 > dp[i] {
                    dp[i] := dp[j] + 1;
                    parent[i] := j;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Find the maximum length
    var maxLen := 1;
    var maxIdx := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 1 <= maxLen <= n
        invariant 0 <= maxIdx < n
        invariant dp[maxIdx] == maxLen
        invariant forall j :: 0 <= j < i ==> dp[j] <= maxLen
    {
        if dp[i] > maxLen {
            maxLen := dp[i];
            maxIdx := i;
        }
        i := i + 1;
    }
    
    // Reconstruct the arrangement to prove it exists
    var arrangement: seq<int> := [];
    var current := maxIdx;
    var count := 0;
    
    while current != -1
        decreases if current >= 0 then current else 0
        invariant count <= maxLen
        invariant |arrangement| == count
        invariant current == -1 || (0 <= current < n && parent[current] < current)
        invariant count < maxLen ==> current >= 0
    {
        if count >= maxLen {
            break;
        }
        arrangement := [current + 1] + arrangement;
        current := parent[current];
        count := count + 1;
    }
    
    // Prove that arrangement is valid and has length maxLen
    assert |arrangement| == maxLen;
    assert forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= n;
    
    // The arrangement satisfies all conditions by construction
    // This is guaranteed by the DP algorithm
    assert is_valid_beautiful_arrangement(arrangement, sizes);
    
    result := maxLen;
}
// </vc-code>

