use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}
// pure-end
// pure-end

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// pure-end

// <vc-helpers>
fn odd_or_zero_exec(x: u32) -> (ret: u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)
    // pre-conditions-start
    requires
        0 < lst.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == add_odd_evens(lst@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sum: u64 = 0;
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            0 < lst.len(),
            sum == add_odd_evens(lst@.subsequence(1, i as int)) as u64,
            i % 2 == 1,
            i <= lst.len(),
    {
        sum = sum + odd_or_zero_exec(lst[i]) as u64;
        proof {
            assert(odd_or_zero_exec(lst[i]) == odd_or_zero(lst@[i as int]));

            // Proving the invariant for the next iteration
            // The invariant states: sum == add_odd_evens(lst@.subsequence(1, i as int)) as u64
            // After updating sum, we need to show:
            // sum' == add_odd_evens(lst@.subsequence(1, (i+2) as int)) as u64
            // where sum' = sum + odd_or_zero_exec(lst[i])
            // and sum = add_odd_evens(lst@.subsequence(1, i as int))
            //
            // Thus, we need to prove:
            // add_odd_evens(lst@.subsequence(1, i as int)) + odd_or_zero(lst@[i as int])
            // == add_odd_evens(lst@.subsequence(1, (i+2) as int))

            // Unfold add_odd_evens(lst@.subsequence(1, (i+2) as int))
            // if i+2 <= lst.len()
            // add_odd_evens(lst@.subsequence(1, (i+2) as int))
            // = odd_or_zero(lst@[1]) + add_odd_evens(lst@.subsequence(1, (i+2) as int).skip(2))
            //   This is not the correct path for the inductive step.

            // Let's use the definition of add_odd_evens.
            // add_odd_evens(s: Seq<u32>) = if s.len() < 2 then 0 else odd_or_zero(s[1]) + add_odd_evens(s.skip(2))

            // Consider the sequence from index 1 to i+2.
            // S_next = lst@.subsequence(1, (i+2) as int)
            // S_current = lst@.subsequence(1, i as int)
            //
            // If i+1 < (i+2), then odd_or_zero(S_next[1]) = odd_or_zero(lst@[1]), odd_or_zero(S_next[i]) = odd_or_zero(lst@[i])
            //
            // We are adding `odd_or_zero_exec(lst[i])` to `sum`.
            // The `add_odd_evens` function sums elements at odd indices (1, 3, 5, ...).
            // So, `lst[i]` where `i` is odd, is correctly processed.
            //
            // The definition of `add_odd_evens` is recursive on `lst.skip(2)`.
            // Our loop increments `i` by 2, processing indices 1, 3, 5, ...
            // This aligns well with `add_odd_evens(lst.skip(2))`.

            // Let S_k = lst@.subsequence(1, k as int)
            // We need to prove:
            // add_odd_evens(S_i) + odd_or_zero(lst@[i as int]) == add_odd_evens(S_{i+2})

            // Base case for add_odd_evens(S_{i+2}):
            // add_odd_evens(S_{i+2}) == odd_or_zero(S_{i+2}[1]) + add_odd_evens(S_{i+2}.skip(2))
            // S_{i+2}[1] corresponds to lst@[1 + (1-1)] = lst@[1]
            // This doesn't match the structure of our loop invariant which is accumulating from index 1.

            // Reconsider the invariant and the definition of add_odd_evens.
            // `add_odd_evens(lst: Seq<u32>)` sums elements at odd indices (1, 3, 5...) relative to THIS sequence.
            // So for `lst@`, it means indices 1, 3, 5, ... of the original list.
            // The invariant `sum == add_odd_evens(lst@.take(i as int).skip(1)) as u64` is problematic.
            // `lst@.take(i as int).skip(1)` means the sequence from index 1 up to i-1.
            // The `add_odd_evens` function operates on the *elements* at index 1, then skips 2, etc. relative to *its own* sequence.

            // Let's analyze `add_odd_evens(lst@)`:
            // `odd_or_zero(lst@[1]) + add_odd_evens(lst@.skip(2))`
            // This correctly sums the element at index 1 and then recursively calls on the remainder starting from index 2.
            // The `remainder` in original list is `lst@[2], lst@[3], ...`. After `skip(2)`, it starts from `lst@[4]`.
            // So `add_odd_evens(lst@)` sums up `lst@[1]`, `lst@[3]`, `lst@[5]`, etc.

            // Our loop variable `i` starts at 1 and increments by 2. It accesses `lst[1]`, `lst[3]`, etc.
            // This perfectly aligns with the `add_odd_evens` calculation.

            // The invariant for sum should reflect the partial sum of `add_odd_evens(lst@)`.
            // `add_odd_evens(lst@)` is `sum_{k=1,3,5,... < N} odd_or_zero(lst@[k])`.
            // After `k` iterations, `i` becomes what the `k`-th odd index is.
            // So after processing `lst[1], lst[3], ..., lst[i-2]`, the `sum` should be:
            // `odd_or_zero(lst@[1]) + odd_or_zero(lst@[3]) + ... + odd_or_zero(lst@[i-2])`.

            // Let `current_sum_spec` be the partial sum of `add_odd_evens(lst@)` up to index `i-2`.
            // This means `add_odd_evens(lst@)` for elements at indices 1, 3, ..., i-2.

            // Let's refine the invariant.
            // `sum == add_odd_evens_up_to_index(lst@, i)`
            // where `add_odd_evens_up_to_index(s: Seq<u32>, current_idx: int)` sums `odd_or_zero(s[k])` for k=1,3,... up to `current_idx-2`.

            // Define a helper spec function for this partial sum.
            #[spec]
            fn add_odd_evens_upto(lst: Seq<u32>, current_idx: int) -> int
                decreases current_idx
            {
                if current_idx < 2 {
                    0
                } else if current_idx == 2 { // Represents having processed only `lst[1]`
                    if lst.len() > 1 { odd_or_zero(lst[1]) } else { 0 }
                } else {
                    odd_or_zero(lst[current_idx - 2]) + add_odd_evens_upto(lst, current_idx - 2)
                }
            }

            // The invariant should be `sum == add_odd_evens_upto(lst@, i as int) as u64`.
            // Initial: i=1. add_odd_evens_upto(lst@, 1) = 0. sum = 0. Holds.

            assert(sum == add_odd_evens_upto(lst@, i as int) as u64);

            let old_i = i;
            let old_sum = sum;
            let new_i = i + 2;

            // Before update: sum == add_odd_evens_upto(lst@, old_i as int) as u64
            // After update: new_sum = old_sum + odd_or_zero_exec(lst[old_i]) as u64
            // We need to prove: new_sum == add_odd_evens_upto(lst@, new_i as int) as u64

            // new_sum = add_odd_evens_upto(lst@, old_i as int) as u64 + odd_or_zero(lst@[old_i as int]) as u64
            // (Assuming odd_or_zero_exec(lst[old_i]) == odd_or_zero(lst@[old_i as int]) proven above)
            //
            // From definition:
            // add_odd_evens_upto(lst@, new_i as int)
            // == odd_or_zero(lst@[new_i as int - 2]) + add_odd_evens_upto(lst@, new_i as int - 2)
            // == odd_or_zero(lst@[old_i as int]) + add_odd_evens_upto(lst@, old_i as int)
            // This exactly matches our `new_sum` after the additions.
            // This proof step is implicit in Verus if the invariant is stated correctly with the definition.
        }
        i = i + 2;
    }
    proof {
        // After loop, i >= lst.len(). And i is odd.
        // We know that `sum == add_odd_evens_upto(lst@, i as int) as u64`.
        // We need to show `sum == add_odd_evens(lst@)`.

        // `add_odd_evens` sums `odd_or_zero` for elements at indices 1, 3, ..., up to `lst.len()-1` (if odd).
        // Since `i` is the first odd index that is `>= lst.len()`,
        // `add_odd_evens_upto(lst@, i as int)` will include all odd indices less than `lst.len()`.

        // If lst.len() is even, say 4. i will be 1, 3, then becomes 5.
        // `add_odd_evens_upto(lst@, 5)` -> odd_or_zero(lst@3) + add_odd_evens_upto(lst@, 3)
        // -> odd_or_zero(lst@3) + odd_or_zero(lst@1) + add_odd_evens_upto(lst@, 1)
        // -> odd_or_zero(lst@3) + odd_or_zero(lst@1) + 0.
        // This is `odd_or_zero(lst@[1]) + odd_or_zero(lst@[3])`.
        // `add_odd_evens(lst@)` for len 4: `odd_or_zero(lst@[1]) + add_odd_evens(lst@.skip(2))`
        // `add_odd_evens(lst@.skip(2))` for `lst@[2], lst@[3]`: `odd_or_zero( (lst@.skip(2))[1] ) + add_odd_evens(lst@.skip(2).skip(2))`
        // means `odd_or_zero(lst@[3]) + add_odd_evens(lst@.skip(4))` which is `0` as length is 0.
        // So they match.

        // If lst.len() is odd, say 5. i will be 1, 3, then becomes 5. (loop condition `i < lst.len()` is false for i=5)
        // So the last processed `i` was 3. After `i=3`, `sum` contains `odd_or_zero(lst@[1]) + odd_or_zero(lst@[3])`.
        // `i` becomes 5. Loop terminates `i < lst.len()` (5 < 5) is false.
        // `add_odd_evens(lst@)` for len 5: `odd_or_zero(lst@[1]) + add_odd_evens(lst@.skip(2))`
        // `add_odd_evens(lst@.skip(2))` for `lst@[2], lst@[3], lst@[4]`: `odd_or_zero(lst@[3]) + add_odd_evens(lst@.skip(4))`
        // `add_odd_evens(lst@.skip(4))` for `lst@[4]`: `0`
        // So `odd_or_zero(lst@[1]) + odd_or_zero(lst@[3])`.
        // The final `sum` matched `add_odd_evens(lst@)`.
        assert(sum == add_odd_evens(lst@) as u64);
    }
    sum
}

#[spec]
fn add_odd_evens_upto(lst: Seq<u32>, current_i: int) -> int
    decreases current_i
{
    if current_i <= 1 { // If current_i is 1, it means we haven't processed anything yet
        0
    } else { // current_i is the next index to be processed (e.g., 3, 5, ...)
        // The last index successfully processed was current_i - 2
        odd_or_zero(lst[current_i - 2]) + add_odd_evens_upto(lst, current_i - 2)
    }
}
// </vc-code>

} // verus!
fn main() {}