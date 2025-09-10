predicate ValidInput(N: int, K: int, S: string)
{
    N > 0 && K >= 0 && |S| == N && 
    forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
}

function StringToBits(S: string): seq<int>
    requires forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
{
    seq(|S|, i requires 0 <= i < |S| => if S[i] == '0' then 0 else 1)
}

predicate ValidResult(result: int, N: int)
{
    0 <= result <= N
}

// <vc-helpers>
function Pow2(k: int): int
    requires k >= 0
    ensures Pow2(k) > 0
{
    if k == 0 then 1 else 2 * Pow2(k-1)
}

function IsPowerOfTwo(n: int): bool
    requires n > 0
{
    (n & (n - 1)) == 0
}

lemma lemma_Pow2_is_power_of_two(k: int)
    requires k >= 0
    ensures IsPowerOfTwo(Pow2(k))
{
    if k == 0 {
        assert Pow2(0) == 1;
        assert (1 & (1-1)) == 0;
    } else {
        Pow2(k-1);
        calc {
            Pow2(k);
            2 * Pow2(k-1);
        }
        var m := Pow2(k-1);
        assert Pow2(k) == 2 * m;
        reveal IsPowerOfTwo();
        assert (m & (m-1)) == 0; // from recursive call
        if m == 1 { // k-1 == 0, so k == 1
          assert 2 * m == 2;
          assert (2 & (2-1)) == 0;
        } else {
          // If m is a power of two and m > 1, then m is even
          // m = 2^j for j > 0
          // 2m = 2^(j+1)
          // (2m) & (2m-1) = 0
          // If m is a power of 2, then m = 2^j for some j >= 0.
          // m-1 is of the form 011...1.
          // m&(m-1) == 0.
          // Also, m is even if j > 0.
          // If m is even, then m-1 is odd.
          // (2m)-1 has the form ...
          // If m = 2^j, then 2m = 2^(j+1).
          // And 2^(j+1) - 1 is a sequence of j+1 ones in binary.
          // 2^(j+1) & (2^(j+1) - 1) == 0.
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, S: string) returns (result: int)
    requires ValidInput(N, K, S)
    ensures ValidResult(result, N)
// </vc-spec>
// <vc-code>
{
    var b = StringToBits(S);
    var current_k := K;
    var max_length := 0;

    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant 0 <= current_k <= K
        invariant 0 <= max_length <= N
        invariant (forall j :: 0 <= j < i && b[j] == 1 ==> exists l :: 0 <= l < j && b[l] == 0) // Ensures that every 1 encountered so far has been "fixed" by a 0 earlier or by spending K
        decreases N - i
    {
        if b[i] == 1 {
            // Need to change this 1 to a 0. Can either use K or look for a preceding 0.
            var found_zero_to_swap := false;
            var j := i - 1;
            while j >= 0 && !found_zero_to_swap
                invariant -1 <= j < i
                invariant !found_zero_to_swap ==> (forall l :: j < l < i ==> b[l] == 1)
                decreases j
            {
                if b[j] == 0 {
                    // Found a 0 at index j. Can swap b[i] and b[j].
                    // This is conceptual; we don't actually modify `b`.
                    // We effectively treat the 1 at `i` as if it were a 0.
                    found_zero_to_swap := true;
                }
                j := j - 1;
            }

            if found_zero_to_swap {
                // If we found a 0 to "swap" with, we conceptually convert this 1 to a 0
                // without spending K. The effective bit at `i` is now 0.
                // The current sequence of 0s continues.
            } else if current_k > 0 {
                // No preceding 0s to swap with, use K to change this 1 to a 0.
                current_k := current_k - 1;
            } else {
                // Cannot make this 1 a 0, so the longest valid run of 0s ends here.
                // Reset max_length calculation for the next run.
                max_length := 0; // This specific loop always counts up; if it hits a 1 it breaks.
                // This `else` branch implies the current bit is effectively 1,
                // and thus breaks any power-of-2 length run.
            }
        }
        i := i + 1;
    }

    // Now we need to find the longest sequence of 0s after the transformations.
    // The problem statement implies we're looking for the longest length L such that
    // L is a power of 2 and there exists a substring of length L consisting of all zeros.
    // We can simulate the transformations greedily.
    var bits_after_ops: seq<int> := b;
    current_k := K;

    var actual_k := K;
    var current_length := 0;
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant 0 <= actual_k <= K
        invariant 0 <= current_length <= N
        invariant (forall j, l :: 0 <= j < i && 0 <= l < j && b[l] == 0 && b[j] == 1 && (forall m :: l < m < j ==> b[m] == 1) ==> actual_k > 0) // conceptual invariant, current_k correctly reflects what we spent
        decreases N - i
    {
        if b[i] == 1 {
            var cost := 0;
            var j := i - 1;
            var ones_count := 0;
            // Iterate backwards to count preceding 1s that would need K
            // This is effectively checking if there's a 0 before a block of 1s
            // that we can "borrow" from.
            while j >= 0 && b[j] == 1
                invariant -1 <= j < i
                decreases j
            {
                ones_count := ones_count + 1;
                j := j - 1;
            }
            // If j < 0, entirely 1s from beginning to i. Cost is 1.
            // If b[j] == 0, then we potentially found a 0 to swap with.
            if j < 0 || b[j] == 1 { // Could not find a 0 before this block of 1s, or j is < 0 means all 1s from start.
                cost := 1;
            } else { // b[j] == 0 and j >= 0
                // We found a 0. This 0 can conceptually move to this position. Cost is 0.
                // However, this logic is tricky. The problem could be interpreted as needing
                // a *fixed* sequence of 0s. Let's simplify.
                // The most straightforward way to use K is to convert a 1 to a 0.
                if actual_k > 0 {
                    actual_k := actual_k - 1;
                    bits_after_ops := bits_after_ops[i := 0]; // conceptually set this bit to 0
                } else {
                    bits_after_ops := bits_after_ops[i := 1]; // remains 1
                }
            }
        } else {
            bits_after_ops := bits_after_ops[i := 0]; // remains 0
        }
        i := i + 1;
    }

    // Now, `bits_after_ops` represents the optimal string. Find the longest power-of-2 length run of 0s.

    max_length := 0;
    current_length := 0;
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant 0 <= current_length <= N
        invariant 0 <= max_length <= N
        invariant forall k' :: 0 <= k' < i && bits_after_ops[k'] == 1 ==> current_length == 0
        decreases N - i
    {
        if b[i] == 0 { // A 0 from the original string
            current_length := current_length + 1;
        } else { // b[i] == 1 (original string)
            // Check if we can change this 1 to a 0
            if K > 0 { // Simplistic, doesn't account for already used K or optimal strategy
                // This requires a more complex DP or greedy approach.
                // The current interpretation is: we can spend K on *any* 1.
                // If we spend K, it functions as a 0.
                // If we don't spend K, it's a 1.
                // The problem is "what is the longest *segment* that can be all zeros"
                // The constraint on K and 0s effectively means we can turn up to K ones into zeros.
                // This is a sliding window problem.
                // Find longest subarray of 0s and 1s such that number of 1s in it is <= K.
                // And the length of this subarray is a power of 2.

                // Let's re-think the strategy for the `solve` function.
                // We need to find the longest window `[start, end)` such that
                // `count(1s in S[start .. end)) <= K` and `(end - start)` is a power of 2.
                // And maximize `end - start`.
            }
            current_length := 0;
        }
        // Update max_length if current_length is a power of two
        // and current_length > max_length.
        if current_length > 0 && IsPowerOfTwo(current_length) && current_length > max_length {
            max_length := current_length;
        }
        i := i + 1;
    }


    // Ok, let's use a sliding window approach with two pointers (left, right).
    // The goal is to maximize `right - left` such that `sum(S[left..right-1]) <= K`
    // (where S[i] is 1 if it's '1', else 0), and `right - left` is a power of 2.

    max_length := 0;
    var left := 0;
    var num_ones := 0;
    i := 0; // right pointer
    while i < N
        invariant 0 <= left <= i <= N
        invariant 0 <= num_ones <= K
        invariant num_ones == (calc sum (j: int) :: if left <= j < i && b[j] == 1 then 1 else 0)
        invariant 0 <= max_length <= N
        decreases N - i
    {
        if b[i] == 1 {
            num_ones := num_ones + 1;
        }

        while num_ones > K
            invariant left < i
            invariant num_ones > K
            invariant num_ones == (calc sum (j: int) :: if left <= j < i && b[j] == 1 then 1 else 0)
            decreases i - left
        {
            if b[left] == 1 {
                num_ones := num_ones - 1;
            }
            left := left + 1;
        }

        // Now, the window [left, i] is valid (num_ones <= K)
        // Check if its length is a power of 2 and if it's the new max.
        var current_window_length := i - left + 1;
        if current_window_length > 0 && IsPowerOfTwo(current_window_length) && current_window_length > max_length {
             max_length := current_window_length;
        }
        i := i + 1;
    }

    result := max_length;
}
// </vc-code>

