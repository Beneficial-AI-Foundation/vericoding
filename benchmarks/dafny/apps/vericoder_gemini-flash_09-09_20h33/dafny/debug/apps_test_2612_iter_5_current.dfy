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
function Max(a: int, b: int): int {
    if a > b then a else b
}

function MaxLengthUpToI(idx: int, dp: seq<int>): int
    requires 0 <= idx < |dp|
    requires forall k :: 0 <= k < |dp| ==> dp[k] >= 0
{
    if idx == 0 then dp[0]
    else Max(dp[idx], MaxLengthUpToI(idx - 1, dp))
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
    var dp := new int[n + 1]; // dp[i] will store the maximum length of a beautiful arrangement ending with index i
    for i := 0 to n {
        dp[i] := 0; // Initialize all to 0
    }

    var max_len := 0;

    for i := 1 to n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k <= n ==> dp[k] >= 0
        invariant max_len == MaxLengthUpToI(i - 1, dp[..i]) || (i == 1 && max_len == 0) // Only considering dp values up to i-1 for max_len
                                                                                        // For i=1, max_len is still 0 before first iteration
    { // Current element is `i` (1-based index)
        // A beautiful arrangement of length 1 ending with `i` always exists
        dp[i] := 1;

        // Try to extend previous arrangements
        for j := 1 to n
            invariant 0 <= j <= n
            invariant forall k :: 0 <= k <= n ==> dp[k] >= 0
            invariant dp[i] >= 1
            // The previous invariant was problematic because it referred to a non-existent variable 'j_prev_loop_iter'
            // and tried to capture a change in dp[i] over an inner loop iteration, which is difficult with simple invariants.
            // The goal of the inner loop is to maximize dp[i], which is captured by the max_len update.
        { // Previous element is `j` (1-based index)
            // Check divisibility: i must be divisible by j OR j must be divisible by i
            // Check size constraint: sizes[j-1] must be less than sizes[i-1] for increasing size
            if (i != j) { // Ensure i and j are distinct in the divisibility/size check
                if (i % j == 0 && sizes[j - 1] < sizes[i - 1]) || (j % i == 0 && sizes[i - 1] < sizes[j - 1]) {
                    if dp[j] + 1 > dp[i] {
                        dp[i] := dp[j] + 1;
                    }
                }
            }
        }
        max_len := Max(max_len, dp[i]);
    }
    result := max_len;
}
// </vc-code>

