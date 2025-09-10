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

predicate IsValidPrefixArrangement(arrangement: seq<int>, sizes: seq<int>, lastIdx: int)
    requires 0 <= lastIdx < |sizes|
    requires |arrangement| >= 1
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
{
    arrangement[|arrangement| - 1] == lastIdx + 1 &&
    is_valid_beautiful_arrangement(arrangement, sizes)
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
    
    // Maintain that dp[j] represents a valid arrangement ending at j+1
    assert forall j :: 0 <= j < n ==> exists arr :: |arr| == dp[j] && IsValidPrefixArrangement(arr, sizes, j);
    
    // For each position i, try to extend arrangements ending at previous positions
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < n ==> 1 <= dp[j] <= n
        invariant forall j :: 0 <= j < n ==> -1 <= parent[j] < j
        invariant forall j :: 0 <= j < n ==> exists arr :: |arr| == dp[j] && IsValidPrefixArrangement(arr, sizes, j)
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant 1 <= dp[i] <= n
            invariant -1 <= parent[i] < i
        {
            // Check if we can extend arrangement ending at j to include i
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
    
    // Reconstruct the arrangement
    var arrangement: seq<int> := [];
    var current := maxIdx;
    var depth := maxLen;
    
    while depth > 0
        invariant 0 <= depth <= maxLen
        invariant |arrangement| == maxLen - depth
        invariant depth == 0 || (0 <= current < n)
        invariant depth > 0 ==> dp[current] == depth
        invariant depth > 0 ==> -1 <= parent[current] < current
        decreases depth
    {
        arrangement := [current + 1] + arrangement;
        current := parent[current];
        depth := depth - 1;
    }
    
    assert |arrangement| == maxLen;
    
    // Verify the arrangement is valid
    assert forall idx :: 0 <= idx < |arrangement| ==> 1 <= arrangement[idx] <= n;
    
    // Verify increasing order
    i := 0;
    while i < |arrangement| - 1
        invariant 0 <= i <= |arrangement| - 1
        invariant forall k :: 0 <= k < i ==> arrangement[k] < arrangement[k + 1]
    {
        assert arrangement[i] < arrangement[i + 1];
        i := i + 1;
    }
    
    // Verify divisibility and size constraints
    i := 0;
    while i < |arrangement| - 1
        invariant 0 <= i <= |arrangement| - 1
        invariant forall k :: 0 <= k < i ==> arrangement[k + 1] % arrangement[k] == 0
        invariant forall k :: 0 <= k < i ==> sizes[arrangement[k] - 1] < sizes[arrangement[k + 1] - 1]
    {
        assert arrangement[i + 1] % arrangement[i] == 0;
        assert sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1];
        i := i + 1;
    }
    
    // Verify distinctness
    i := 0;
    while i < |arrangement|
        invariant 0 <= i <= |arrangement|
        invariant forall p, q :: 0 <= p < q < i ==> arrangement[p] != arrangement[q]
    {
        var j := i + 1;
        while j < |arrangement|
            invariant i + 1 <= j <= |arrangement|
            invariant forall q :: i < q < j ==> arrangement[i] != arrangement[q]
        {
            assert arrangement[i] != arrangement[j];
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert is_valid_beautiful_arrangement(arrangement, sizes);
    
    result := maxLen;
}
// </vc-code>

