predicate ValidInput(N: int, A: seq<int>, B: seq<int>, C: seq<int>)
{
    N >= 1 &&
    |A| == N &&
    |B| == N &&
    |C| == N - 1 &&
    (forall i :: 0 <= i < N ==> 1 <= A[i] <= N) &&
    (forall i, j :: 0 <= i < j < N ==> A[i] != A[j])
}

function SumSatisfaction(A: seq<int>, B: seq<int>, C: seq<int>, N: int): int
    requires N >= 1
    requires |A| == N
    requires |B| == N
    requires |C| == N - 1
    requires forall i :: 0 <= i < N ==> 1 <= A[i] <= N
{
    SumSatisfactionUpTo(A, B, C, N)
}

function SumSatisfactionUpTo(A: seq<int>, B: seq<int>, C: seq<int>, k: int): int
    requires 0 <= k <= |A|
    requires |B| == |A|
    requires |C| == |A| - 1
    requires forall i :: 0 <= i < |A| ==> 1 <= A[i] <= |A|
{
    if k == 0 then 0
    else
        var prevSum := SumSatisfactionUpTo(A, B, C, k-1);
        var baseContrib := B[A[k-1] - 1];
        var bonusContrib := if k > 1 && A[k-1] == A[k-2] + 1 then C[A[k-1] - 2] else 0;
        prevSum + baseContrib + bonusContrib
}

// <vc-helpers>
function SumSatisfactionIterative(k: int, A: seq<int>, B: seq<int>, C: seq<int>): int
    requires 0 <= k <= |A|
    requires |B| == |A|
    requires |C| == |A| - 1
    requires forall i :: 0 <= i < |A| ==> 1 <= A[i] <= |A|
    ensures SumSatisfactionIterative(k, A, B, C) == SumSatisfactionUpTo(A, B, C, k)
{
    if k == 0 then 0
    else
        var prevSum := SumSatisfactionIterative(k - 1, A, B, C);
        var baseContrib := B[A[k-1] - 1];
        var bonusContrib := if k > 1 && A[k-1] == A[k-2] + 1 then C[A[k-1] - 2] else 0;
        prevSum + baseContrib + bonusContrib
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: seq<int>, B: seq<int>, C: seq<int>) returns (result: int)
    requires ValidInput(N, A, B, C)
    ensures result == SumSatisfaction(A, B, C, N)
// </vc-spec>
// <vc-code>
{
    var currentSum := 0; 
    for k := 0 to N
        invariant 0 <= k <= N
        invariant currentSum == SumSatisfactionIterative(k, A, B, C)
    {
        if k > 0 { // This condition 'k > 0' is redundant here because k starts from 0 so in the first iteration (k=0) it will be skipped, but the invariant must hold.
                   // The update to currentSum should only happen when k advances from k-1 to k. 
                   // The correct way to implement this is to compute the (k-1)-th term contribution in the (k-1)-th iteration itself.
                   // So, the loop should go from k=1 to N, calculating the k-th contribution.
                   // Or, if k goes from 0 to N-1, calculate for k-th element.
                   // Let's use k as the index for the element currently being processed (A[k]).
                   // If the loop iterates from k=0 to N-1 and calculates currentSum correctly at each step,
                   // then at the end, currentSum should be SumSatisfactionIterative(N, ...).
                   // The definition of SumSatisfactionIterative uses k as the upper bound of the sequence processed.
                   // So k == 0 implies 0 elements processed.
                   // The loop invariant `currentSum == SumSatisfactionIterative(k, A, B, C)`
                   // means that `currentSum` stores the sum up to `k` elements.
                   // In the iteration `k`, we compute the sum up to `k` elements.
                   // So when `k` is incremented, `currentSum` must represent `SumSatisfactionIterative(old_k+1, A, B, C)`.
                   // The old code: `currentSum` is `SumSatisfactionIterative(old_k, A, B, C)`.
                   // Then it adds the `old_k`-th element's contribution.
                   // `baseContrib` and `bonusContrib` are for `A[k-1]`.
                   // This implies that inside the loop for `k`, we are calculating the `k`-th element's contribution to the sum.
                   // So if `k` is the loop variable, it refers to the `k`-th element.
                   // Thus, when we are in the loop `k` and we calculate `A[k-1]`, it means the `k`-th effective element.
                   // When the loop finishes for `k`, `currentSum` should be `SumSatisfactionIterative(k_next, ...)`.
                   // Let's re-align the loop to process `k-1` in the `k`th iteration.
        
            // The original logic assumes k is the number of elements processed thus far.
            // When k=0, 0 elements processed, sum = 0.
            // When k=1, we process A[0].
            // When k=i, we process A[i-1].
            // The loop invariant is `currentSum == SumSatisfactionIterative(k, A, B, C)`.
            // When we enter the loop with variable `k`, `currentSum` correctly has `SumSatisfactionIterative(k, A, B, C)`.
            // The update to `currentSum` inside the loop should calculate the sum for `k+1`.
            // So `k` in the loop needs to be the index of the element being *added* in that iteration.
            // The loop variable `k` in `for k := 0 to N` means `k` will take values 0, 1, ..., N.
            //
            // If `k` in the loop is the count of elements already processed, then inside the loop body, we are preparing for `k+1`.
            // The original code was almost correct, just missing the observation that when `k` is incremented, the `currentSum` needs to be updated.
            // The original code uses `k` as the upper bound of the sum.
            // Thus, when `k` iterates from 0 to N, in iteration `k`, `currentSum` holds the sum for `k` elements.
            // When `k` becomes `k+1`, then `currentSum` should have `SumSatisfactionIterative(k+1, A, B, C)`.
            // The missing piece is the addition of the (k-th) element.
            // The for-loop iterates k from 0 to N.
            // In iteration k:
            //   - k=0: currentSum is 0. Satisfies invariant.
            //   - k=1: previous currentSum was 0 (for k=0). Now we compute for A[0]. 
            //     baseContrib = B[A[0]-1]. bonusContrib = 0 because k (which is 1) is not > 1.
            //     currentSum = 0 + B[A[0]-1].
            //     This should be SumSatisfactionIterative(1, A, B, C). This is correct.
            //   - k=i: currentSum has SumSatisfactionIterative(i-1, A, B, C).
            //     We need to compute the i-th element's contribution. That element is A[i-1].
            //     baseContrib = B[A[i-1]-1].
            //     bonusContrib = if i > 1 && A[i-1] == A[i-2] + 1 then C[A[i-1]-2] else 0.
            //     currentSum = currentSum + baseContrib + bonusContrib.
            //     This correctly updates `currentSum` to `SumSatisfactionIterative(i, A, B, C)`.
            //
            // The problem is that the loop invariant is checked at the *start* of the loop, before the increment to `k+1`.
            // When `k` is 0, `currentSum` is 0. Invariant `currentSum == SumSatisfactionIterative(0, ...)`, which is true.
            // When `k` is 1, `currentSum` (before the block) is `SumSatisfactionIterative(0, ...)`.
            // But the invariant states `currentSum == SumSatisfactionIterative(k, ...)`.
            // So for `k=1`, `currentSum` should already be `SumSatisfactionIterative(1, ...)`.
            // The body needs to be structured differently.

            // Let's refine the loop: `k` will represent the index of the element being *added* to the sum.
            // Loop from `k=0` to `N-1` (inclusive) for adding `A[k]`.
            // `currentSum` will represent sum up to `A[k]`
            
            // Re-think the loop variable `k` and the invariant `currentSum == SumSatisfactionIterative(k, A, B, C)`.
            // This means that at the beginning of an iteration where the loop variable is `k_loop_var`, 
            // `currentSum` should be equal to `SumSatisfactionIterative(k_loop_var, A, B, C)`.
            // The loop runs for `k_loop_var` from `0` to `N`.
            // When `k_loop_var` is `0`, `currentSum` is initialized to `0`. `SumSatisfactionIterative(0, ...) == 0`. Invariant holds.
            //
            // Iteration `k_loop_var` (let's just call it `k` for simplicity as in the original code, but remember it's the loop variable).
            // At the start of the current iteration, `currentSum` is `SumSatisfactionIterative(k, A, B, C)`.
            // The goal is that when `k` becomes `k+1` for the next iteration, `currentSum` has been updated to `SumSatisfactionIterative(k+1, A, B, C)`.
            // This means that inside the loop, the `k+1`-th contribution (which uses `A[k]`) should be added.
            // The actual computation of `baseContrib` and `bonusContrib` is using `A[k-1]` and `A[k-2]`.
            // So if my loop variable is `k`, then `A[k-1]` is what gets added in this iteration to get to `SumSatisfactionIterative(k)`.
            //
            // The problem is that the invariant `currentSum == SumSatisfactionIterative(k, A, B, C)` is checked *at the beginning of the loop iteration* for `k`.
            // But the *update* `currentSum := currentSum + baseContrib + bonusContrib` in the loop body computes the sum for the *next* `k`.
            //
            // Let's reconsider. The `for k := lo to hi` loop means that the body is executed for `k = lo, lo+1, ..., hi`.
            // The invariant must hold before each iteration `k`.
            // When `k=0`: `currentSum=0`. `SumSatisfactionIterative(0,...) = 0`. Invariant holds.
            //
            // Inside the loop: we are calculating the value `SumSatisfactionIterative(k+1,...)`.
            // The contribution for `k+1` from the definition is based on `A[k]`.
            //
            // The `if k > 0` condition.
            // When `k=0`, we skip. `currentSum` remains `0`.
            // When loop iterator increments to `k=1`, the invariant needs `currentSum == SumSatisfactionIterative(1, A, B, C)`.
            // But `currentSum` is still `0`. This is where the invariant fails.
            //
            // The fix is to ensure `currentSum` is correctly updated *before* the loop variable `k` increments.
            //
            // The loop should iterate `k` from `0` to `N-1`. In each iteration `k`, we add the contribution of `A[k]`.
            // `currentSum` will then hold `SumSatisfactionIterative(k+1, A, B, C)`.

            // New logic: `k` iterates from `0` to `N-1`.
            // At iteration `k`: `currentSum` has `SumSatisfactionIterative(k, A, B, C)`.
            // We want to update `currentSum` to `SumSatisfactionIterative(k+1, A, B, C)`.
            // This requires adding the terms from `A[k]`.

    var currentSum := 0; // Represents SumSatisfactionUpTo(A, B, C, k) at the start of the loop
    for k_index := 0 to N-1 // k_index goes from 0 to N-1, representing A[k_index]
        invariant 0 <= k_index <= N
        invariant currentSum == SumSatisfactionIterative(k_index, A, B, C) // currentSum == SumSatisfactionUpTo(k_index)
    {
        // currentSum is SumSatisfactionIterative(k_index, A, B, C)
        var baseContrib := B[A[k_index] - 1]; // Contribution from A[k_index]
        var bonusContrib := 0;
        if k_index > 0 && A[k_index] == A[k_index - 1] + 1 {
            bonusContrib := C[A[k_index] - 2];
        }
        currentSum := currentSum + baseContrib + bonusContrib;
        // After this, currentSum is SumSatisfactionIterative(k_index + 1, A, B, C)
    }
    // Loop finishes. k_index is N.
    // currentSum is SumSatisfactionIterative(N, A, B, C).
    return currentSum;
}
// </vc-code>

