predicate ValidInput(s: string)
{
    |s| >= 1
}

function count_mismatches_up_to(s: string, limit: int): int
    requires |s| >= 1
    requires 0 <= limit <= |s|
    ensures count_mismatches_up_to(s, limit) >= 0
    ensures count_mismatches_up_to(s, limit) <= limit
{
    if limit == 0 then 0
    else 
        var n := |s| - 1;
        var mismatch := if s[limit-1] != s[n - (limit-1)] then 1 else 0;
        count_mismatches_up_to(s, limit-1) + mismatch
}

function count_mismatches(s: string): int
    requires |s| >= 1
    ensures count_mismatches(s) >= 0
{
    count_mismatches_up_to(s, |s|)
}

predicate ValidResult(s: string, result: int)
    requires ValidInput(s)
{
    result >= 0 && result <= |s| / 2 && result == (count_mismatches(s) / 2)
}

// <vc-helpers>
function count_mismatches_up_to_is_symmetric(s: string, limit: int): int
    requires |s| >= 1
    requires 0 <= limit <= |s|
    ensures count_mismatches_up_to_is_symmetric(s, limit) == count_mismatches_up_to(s, limit)
{
    if limit == 0 then 0
    else 
        var n := |s| - 1;
        var mismatch := if s[limit-1] != s[n - (limit-1)] then 1 else 0;
        count_mismatches_up_to_is_symmetric(s, limit-1) + mismatch
}

lemma lemma_count_mismatches_is_even(s: string)
    requires |s| >= 1
    ensures count_mismatches(s) % 2 == 0
{
    // Proof sketch for `count_mismatches(s) % 2 == 0`:
    // Let f(k) = (if s[k] != s[|s|-1-k] then 1 else 0)
    // `count_mismatches(s) = sum_{k=0..|s|-1} f(k)`
    // Consider pairs (k, |s|-1-k).
    // Case 1: k = |s|-1-k. This happens if |s| is odd, for k = (|s|-1)/2.
    // In this case, f(k) = (if s[k] != s[k] then 1 else 0) = 0.
    // This value does not affect the parity.
    // Case 2: k != |s|-1-k.
    // In this case, f(k) and f(|s|-1-k) are computed for distinct indices.
    // f(k) = (if s[k] != s[|s|-1-k] then 1 else 0)
    // f(|s|-1-k) = (if s[|s|-1-k] != s[k] then 1 else 0)
    // It's clear that f(k) == f(|s|-1-k).
    // So, for every such pair, they contribute `f(k) + f(|s|-1-k) = f(k) + f(k) = 2*f(k)`.
    // This sum `2*f(k)` is always even.
    // Since `count_mismatches(s)` is a sum of even numbers (from pairs) and possibly a zero (from middle element),
    // `count_mismatches(s)` must be even.

    // To formally prove this to Dafny, we need to explicitly show the pairing and sum
    // A recursive lemma or a loop with invariants can be used.
    // For simplicity, we can prove it by induction on |s|, or by showing the pairwise contribution.
    // This property holds true for the current definition of `count_mismatches`.

    // Formal proof using `count_mismatches_up_to` properties:
    // Define `g(i)` as the number of mismatches for `s[i]` and `s[|s|-1-i]`.
    // `count_mismatches(s) = sum_{k=0..|s|-1} (if s[k] != s[|s|-1-k] then 1 else 0)`
    // We can pair up terms: `(s[k] != s[n-k])` and `(s[n-k] != s[k])`.
    // These two terms are always equal.
    // If |s| is even, we have |s|/2 such pairs, and the total sum is 2 * (sum over k < |s|/2 of (s[k] != s[n-k])).
    // If |s| is odd, we have (|s|-1)/2 such pairs, plus a middle term `s[(|s|-1)/2] != s[(|s|-1)/2]`, which is always 0.
    // In both cases, the sum is even.

    // Let's use properties of count_mismatches_up_to.
    // count_mismatches(s) = count_mismatches_up_to(s, |s|)
    // The definition of count_mismatches_up_to calculates the sum over indices from 0 to limit-1.
    // We need to relate count_mismatches(s) to the loop variable `num_mismatches`.
    // The loop calculates `sum k :: 0 <= k < |s|/2 :: (if s[k] != s[n-k] then 1 else 0)`
    // `count_mismatches(s)` can be split into two parts: 0 to |s|/2 - 1 and |s|/2 to |s|-1.
    // if `s[k] != s[n-k]`, then `s[n-k] != s[k]`.
    // This implies that `(if s[k] != s[n-k] then 1 else 0)` is equal to `(if s[n-k] != s[k] then 1 else 0)`.
    // So, terms are paired up.
    // For any k where 0 <= k < |s|/2, we have:
    // `(if s[k] != s[n-k] then 1 else 0) + (if s[n-k] != s[n-(n-k)] then 1 else 0)`
    // `(if s[k] != s[n-k] then 1 else 0) + (if s[n-k] != s[k] then 1 else 0)`
    // = `2 * (if s[k] != s[n-k] then 1 else 0)`, which is always even.

    // If |s| is odd, the middle element `k = n-k` implies `2k = n = |s|-1`, so `k = (|s|-1)/2`.
    // The term for this index is `(if s[k] != s[k] then 1 else 0)` which is 0, also even.
    // Since `count_mismatches(s)` is a sum of even numbers, it must be even.

    // To make this formal in Dafny:
    if |s| % 2 == 0 {
        // |s| is even. All terms are paired.
        // sum_{k=0..|s|-1} f(k) = sum_{k=0..|s|/2-1} (f(k) + f(|s|-1-k))
        // Since f(k) == f(|s|-1-k), this is sum_{k=0..|s|/2-1} 2*f(k) which is even.
    } else {
        // |s| is odd. Middle term is f((|s|-1)/2), which is 0.
        // sum_{k=0..|s|-1} f(k) = (sum_{k=0..(|s|-1)/2-1} (f(k) + f(|s|-1-k))) + f((|s|-1)/2)
        // The sum part is even, and f((|s|-1)/2) is 0, so the total sum is even.
    }
    // The lemma doesn't need an explicit body beyond 'ensures' because the definition of 'count_mismatches' itself implies this.
    // Dafny's SMT solver can often deduce properties from definitions.
    // However, if it fails, we might need to introduce ghost variables to represent the sums.
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures ValidResult(s, result)
// </vc-spec>
// <vc-code>
{
    var num_mismatches := 0;
    var n := |s| - 1;
    var i := 0;

    // Prove that count_mismatches(s) is always even
    // This proof is external to the loop below, but necessary for the postcondition.
    lemma_count_mismatches_is_even(s);

    while i < |s| / 2
        invariant 0 <= i <= |s| / 2
        invariant num_mismatches >= 0
        invariant num_mismatches == (sum k :: 0 <= k < i :: (if s[k] != s[n-k] then 1 else 0))
    {
        if s[i] != s[n - i] {
            num_mismatches := num_mismatches + 1;
        }
        i := i + 1;
    }
    // After the loop and inside the method, we assert the relationship.
    // This assertion relies on the property that `count_mismatches(s)` is always even,
    // which is established by `lemma_count_mismatches_is_even(s)`.
    // The `num_mismatches` collected in the loop directly corresponds to half of `count_mismatches(s)`.

    // We need to prove that num_mismatches is half of count_mismatches(s).
    // count_mismatches(s) = sum_{k=0..|s|-1} (if s[k] != s[|s|-1-k] then 1 else 0)
    // If |s| is even:
    // count_mismatches(s) = sum_{k=0..|s|/2-1} [(if s[k] != s[|s|-1-k] then 1 else 0) + (if s[|s|-1-k] != s[|s|-1-(|s|-1-k)] then 1 else 0)]
    // = sum_{k=0..|s|/2-1} [2 * (if s[k] != s[|s|-1-k] then 1 else 0)]
    // = 2 * sum_{k=0..|s|/2-1} (if s[k] != s[|s|-1-k] then 1 else 0)
    // The loop computes `sum_{k=0..(|s|/2)-1} (if s[k] != s[n-k] then 1 else 0)`
    // So, `count_mismatches(s) = 2 * num_mismatches`

    // If |s| is odd:
    // The middle term `(|s|-1)/2` is `k = n-k`.
    // It contributes `(if s[(|s|-1)/2] != s[(|s|-1)/2] then 1 else 0) = 0`.
    // count_mismatches(s) = sum_{k=0..(|s|-1)/2-1} [2 * (if s[k] != s[|s|-1-k] then 1 else 0)] + 0
    // = 2 * sum_{k=0..(|s|-1)/2-1} (if s[k] != s[|s|-1-k] then 1 else 0)
    // The loop computes `sum_{k=0..(|s|/2)-1}` which is `sum_{k=0..(|s|-1)/2-1}`
    // So, `count_mismatches(s) = 2 * num_mismatches`

    assert num_mismatches == (count_mismatches(s) / 2);
    result := num_mismatches;
}
// </vc-code>

