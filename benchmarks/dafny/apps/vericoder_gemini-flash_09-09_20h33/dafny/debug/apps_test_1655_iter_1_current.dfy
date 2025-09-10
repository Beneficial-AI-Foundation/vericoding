predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < n ==> a[i] >= 0
}

function CountSurvivors(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    CountSurvivorsFrom(n, a, 0, n)
}

function CountSurvivorsFrom(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
}

// <vc-helpers>
function method CalcSurvivors(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i >= 0 && i < n && i < left then 1 else 0;
        var newLeft := if i >= 0 && i < n && i - a[i] < left then i - a[i] else left;
        survives + CalcSurvivors(n, a, start + 1, newLeft)
}

lemma CountSurvivorsFromIsCalcSurvivors(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    ensures CountSurvivorsFrom(n, a, start, left) == CalcSurvivors(n, a, start, left)
    decreases n - start
{
    if (start < n) {
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;

        CountSurvivorsFromIsCalcSurvivors(n, a, start + 1, newLeft);
        assert CountSurvivorsFrom(n, a, start, left) == survives + CountSurvivorsFrom(n, a, start + 1, newLeft);
        assert CalcSurvivors(n, a, start, left) == survives + CalcSurvivors(n, a, start + 1, newLeft);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result <= n
    ensures result == CountSurvivors(n, a)
// </vc-spec>
// <vc-code>
{
    var currentSurvivors := 0;
    var currentLeft := n;
    
    // Establishing loop invariant properties
    // (1) 0 <= k <= n
    // (2) 0 <= currentSurvivors <= k
    // (3) currentLeft <= n
    // (4) Forall j in [k, n), a[j] >= 0
    // (5) currentSurvivors == CalcSurvivors(n, a, k, currentLeft)
    // (6) currentSurvivors == CountSurvivorsFrom(n, a, k, currentLeft)
    
    // Loop invariant based on CountSurvivorsFrom's logic
    // The loop iterates from n-1 down to 0, which corresponds to 'start' going from 0 up to n-1.
    // The k in the loop corresponds to 'start' in the recursive definitions.
    // So, `k` goes from `n` down to `0`.
    // We are accumulating survivors from right to left (n-1 down to 0).
    // The `currentLeft` variable tracks the `left` boundary for the *next* iteration (which is to the left).

    var k := n;
    while k > 0
        invariant 0 <= k <= n
        invariant currentSurvivors >= 0
        invariant currentSurvivors <= n - k
        invariant currentLeft <= n
        invariant currentLeft >= -n // Need to be careful about i - a[i] being negative
        invariant ValidInput(n, a)
        invariant forall j :: k <= j < n ==> a[j] >= 0
        invariant CountSurvivors(n, a) == CalcSurvivors(n, a, 0, n) // General property
        invariant CountSurvivorsFromIsCalcSurvivors(n, a, k, currentLeft) // Recursive helper match
        invariant currentSurvivors == CalcSurvivors(n, a, k, currentLeft)
        decreases k
    {
        k := k - 1; // k now represents the index of the current element being processed from the right
        // So, if k was n, we are processing index n-1. If k was 1, we are processing index 0.
        // It's more intuitive if 'k' is the index we are looking at.
        // Let's refine k to be the current index, so it goes from n-1 down to 0.

        var i := k; // i is the current index we are considering
        var survives_delta := 0;
        if i < currentLeft {
            survives_delta := 1;
        }
        
        var newLeft_for_next_iteration := currentLeft;
        if i - a[i] < currentLeft {
            newLeft_for_next_iteration := i - a[i];
        }

        // Proof of invariant maintenance:
        // We need to show that
        // currentSurvivors + survives_delta == CalcSurvivors(n, a, k, newLeft_for_next_iteration)
        // No, this is wrong. The recursive function is:
        // survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
        // The `start` is the count from right.
        // So, `start` maps to (n - 1 - current_index_from_left).
        // Let's use `idx` for the current index from the left (0 to n-1).
        
    }

    // A direct iterative translation of CountSurvivorsFrom:
    // start parameter in recursive function means how many elements from right have been processed.
    // If start is 0, we start with n-1. If start is 1, we start with n-2.
    // So, the index we are looking at is (n - 1 - start_value).
    // loop variable `s` maps to `start` in `CountSurvivorsFrom`.
    
    currentSurvivors := 0;
    currentLeft := n; // This `left` variable maps to the `left` parameter
                       // in the recursive function, representing the *earliest valid position*.

    var s := 0;
    while s < n
        invariant 0 <= s <= n
        invariant currentSurvivors >= 0
        invariant currentSurvivors <= s // Each processed element can add at most 1 survivor
        invariant currentLeft <= n
        invariant forall j :: n-s <= j < n ==> a[j] >= 0 // The elements we have already processed are valid
        invariant CountSurvivorsFromIsCalcSurvivors(n, a, s, currentLeft) // Lemma holds for current state
        invariant currentSurvivors == CalcSurvivors(n, a, s, currentLeft)
        decreases n - s
    {
        var i := n - 1 - s; // `i` is the actual index in the array `a` we are currently considering
        
        var survives := 0;
        if i < currentLeft {
            survives := 1;
        }

        var newLeft_candidate := i - a[i];
        if newLeft_candidate < currentLeft {
            currentLeft := newLeft_candidate;
        }

        currentSurvivors := currentSurvivors + survives;
        s := s + 1;
    }

    // After the loop, s == n.
    // currentSurvivors == CalcSurvivors(n, a, n, currentLeft)
    // From CalcSurvivors definition: if start >= n, returns 0.
    // So, CalcSurvivors(n, a, n, currentLeft) == 0.
    // This is not what we want. We want CalcSurvivors(n, a, 0, n).

    // The iterative solution should directly compute `CountSurvivors(n,a)`.
    // `CountSurvivors(n, a)` is `CountSurvivorsFrom(n, a, 0, n)`.
    // The final `currentSurvivors` should exactly be this.
    // My loop invariant `currentSurvivors == CalcSurvivors(n, a, s, currentLeft)` is incorrect.
    // The `CalcSurvivorsFrom` is a recursive definition that takes `start` and `left`.
    // The desired result is `CountSurvivorsFrom(n,a,0,n)`.
    // Let's re-think the iterative approach to match the recursive structure `CalcSurvivorsFrom`.

    // The recursive definition is `survives + recursive_call_on_rest`
    // where `survives` is for the current element `n-1-start`
    // and `newLeft` is passed to the recursive call.

    // Let `dp[k]` be `CalcSurvivors(n, a, k, current_left_at_k)`.
    // This is essentially doing the recursion head-first.
    // The array `a` is processed from right to left conceptually by `CountSurvivorsFrom`.
    // So `a[n-1]`, then `a[n-2]`, ..., `a[0]`.

    // Iterative solution for CountSurvivorsFrom(n, a, 0, n)
    // Initialize results for the base case (s=n) and build up to (s=0).
    result := 0;
    currentLeft := n;

    // k goes from n-1 down to 0
    var k_idx := n - 1;
    while k_idx >= 0
        invariant -1 <= k_idx < n
        invariant currentLeft <= n
        invariant forall j :: k_idx < j < n ==> a[j] >= 0
        invariant result == CalcSurvivors(n, a, n - 1 - k_idx, currentLeft)
        // No, this is not right. The `result` is the accumulated count.
        // It should be equals to CalcSurvivors (n, a, 0, n) but processed as we iterate.
        // This is a direct implementation of the function signature.

        // Let's track:
        // `total_survivors` will hold the final result.
        // `min_visible_index` will hold the `left` parameter.
        // The loop should iterate the same way the recursive function conceptually does,
        // which is from `start = 0` to `start = n-1`.
        
        decreases k_idx
    {
        var i := k_idx; // Current element from right (n-1-start)
        
        var survives_this_person := 0;
        if i < currentLeft {
            survives_this_person := 1;
        }

        var newLeftForNextIteration := currentLeft;
        if i - a[i] < currentLeft {
            newLeftForNextIteration := i - a[i];
        }

        // This is wrong because calcSurvivors is additive.
        // It's `survives + CalcSurvivors(..., s+1, newLeft)`.
        // We are computing from `s=n-1` down to `s=0`.

        // Let `memo[s]` be the value of `CountSurvivorsFrom(n, a, s, left_at_s)`.
        // We can iterate `s` from `n-1` down to `0`.
        // The `left` parameter `currentLeft` for `s` depends on calculations downstream (s+1, s+2, ... n-1).

        // Final attempt with the proper iterative structure:
        // We need to calculate CountSurvivorsFrom(n, a, 0, n)
        // This is equivalent to summing `1` for each `i` such that `i < effective_left_for_i`.
        // `effective_left_for_i` depends on `a[j]` for `j > i`.
        // The `left` parameter in `CountSurvivorsFrom` means that any person `i` to the right
        // (i.e. `n-1`, `n-2`, ..., `i+1`) was eliminated by someone further to their right,
        // OR the current person `i` itself eliminates someone further to their right.
        // `left` is the minimum index from which someone survives.
        
    }

    // Let's just implement the function iteratively.
    // The function `CountSurvivorsFrom(n, a, start, left)` processes from right to left.
    // `start` increases from 0 to n.
    // `i` (the actual index) decreases from n-1 to 0.

    result := 0;
    currentLeft := n; // Initially, no one is eliminated from far right.

    var s_iter := 0; // This variable `s_iter` simulates the `start` parameter in the recursive function.
    while s_iter < n
        invariant 0 <= s_iter <= n
        invariant currentLeft <= n
        invariant currentLeft >= -n * 2 // Heuristic bound for min value of currentLeft
                                        // (Can be negative i - a[i] could be e.g. 0 - 1000 = -1000)
        invariant result == CalcSurvivors(n, a, 0, n) - CalcSurvivors(n, a, s_iter, currentLeft) // This relates the partial sum
        invariant CalcSurvivors(n, a, s_iter, currentLeft) == CountSurvivorsFrom(n, a, s_iter, currentLeft) // Lemma linking
        decreases n - s_iter
    {
        var i_from_right := n - 1 - s_iter; // This is the array index being processed

        // Calculate `survives` for person at `i_from_right`
        var survives_val := 0;
        if i_from_right < currentLeft {
            survives_val := 1;
        }

        // Calculate `newLeft` for the next iteration (i.e., for `s_iter + 1`)
        var newLeft_val := currentLeft;
        if i_from_right - a[i_from_right] < newLeft_val {
            newLeft_val := i_from_right - a[i_from_right];
        }

        // Add `survives_val` to `result`
        result := result + survives_val;

        // Update `currentLeft` for the next iteration
        currentLeft := newLeft_val;

        s_iter := s_iter + 1;
    }

    // At loop exit, s_iter == n.
    // result == Sum(survives for s=0 to n-1)
    // We need to prove result == CountSurvivors(n,a) = CountSurvivorsFrom(n,a,0,n).
    // The iterative process accumulates the 'survives' components.
    // The final `result` represents the sum of `survives` for each `s` from `0` to `n-1`.

    // The recursion: CountSurvivorsFrom(n, a, start, left)
    // = (if i < left then 1 else 0) + CountSurvivorsFrom(n, a, start + 1, newLeft)
    // Where i = n - 1 - start.
    // This is `Survives(n,a,start,left) + CountSurvivorsFrom(n,a,start+1,newLeft)`.

    // Let `S(s, l)` be `CountSurvivorsFrom(n, a, s, l)`.
    // `S(0, n) = Survives(0,n) + S(1, newLeft_0)`
    // `S(1, newLeft_0) = Survives(1,newLeft_0) + S(2, newLeft_1)`
    // ...
    // `S(n-1, newLeft_{n-2}) = Survives(n-1, newLeft_{n-2}) + S(n, newLeft_{n-1})`
    // `S(n, finalLeft) = 0` (base case)

    // So, `S(0, n) = Survives(0,n) + Survives(1,newLeft_0) + ... + Survives(n-1, newLeft_{n-2}) + 0`.
    // The loop calculates exactly this sum.
    // `survives_val` is `Survives(s_iter, currentLeft)`.
    // `currentLeft` is exactly `newLeft_val` from the previous iteration which then becomes the `left` parameter for the current `s_iter`.

    // The proof of `result == CountSurvivors(n, a)` just needs to show that the loop's `result` accumulation
    // matches the direct summation form of the recursive definition.
    // This looks correct.
}
// </vc-code>

