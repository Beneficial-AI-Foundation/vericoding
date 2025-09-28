// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed the postcondition in the else branch to correctly append the element at m[0] for the corresponding flipped position. */
function flipudRecursive(m: seq<real>, k: int): seq<real>
    requires 0 <= k <= |m|
    ensures |flipudRecursive(m, k)| == k
    ensures forall i :: 0 <= i < k ==> flipudRecursive(m, k)[i] == m[k - 1 - i]
{
    if k == 0 then []
    else
    (
        var recResult := flipudRecursive(m, k - 1);
        // The previous postcondition for recResult was: forall i :: 0 <= i < k-1 ==> recResult[i] == m[(k-1) - 1 - i]
        // We want to construct the new sequence such that its i-th element is m[k - 1 - i]
        // The new element for the k-th position in the overall flipped sequence is m[|m| - k] (relative to the original m)
        // But here, it's relative to the subsequence m[0...k-1].
        // The i-th element of flipudRecursive(m,k) should be m[k-1-i].
        // The k-th element (index k-1) of flipudRecursive(m,k) should be m[k-1 - (k-1)] == m[0].
        // The (k-1)-th element (index k-2) of flipudRecursive(m,k) should be m[k-1 - (k-2)] == m[1].
        // What's being recursively built is the *reversed* prefix.
        // So, if recResult is m[k-2], m[k-3], ..., m[0]
        // and we want m[k-1], m[k-2], ..., m[0]
        // We need to prepend m[k-1] to the result of flipudRecursive(m, k-1)
        // No, this is incorrect. The recursive call constructs a sequence of length k-1.
        // Its last element will be m[0]. Its first element will be m[k-2].
        // When we append m[k-1] to the end of recResult, we get a sequence where:
        // recResult[j] = m[k-1-1-j] for j < k-1
        // (recResult + [m[k-1]])[j] = m[k-2-j] for j < k-1
        // (recResult + [m[k-1]])[k-1] = m[k-1]
        // This is not what we want. We want the j-th element to be m[k-1-j].
        // The recursive step should be to prepend the correct element m[k-1] to the recursively flipped rest.
        // But the definition uses specific 'k' for indexing into 'm'.
        // The `k` in `flipudRecursive(m, k)` means the number of elements to flip from `m`,
        // taking `m[0]` to `m[k-1]` as the source range.

        // Let's analyze the postcondition for flipudRecursive(m, k)
        // ensures forall i :: 0 <= i < k ==> flipudRecursive(m, k)[i] == m[k - 1 - i]

        // Base case k=0: [] which satisfies length 0 and empty forall.

        // Inductive step for k:
        // recResult := flipudRecursive(m, k - 1)
        // By induction hypothesis:
        // |recResult| == k - 1
        // forall i :: 0 <= i < k - 1 ==> recResult[i] == m[(k-1) - 1 - i] == m[k - 2 - i]

        // We want flipudRecursive(m, k) to have length k and:
        // forall i :: 0 <= i < k ==> flipudRecursive(m, k)[i] == m[k - 1 - i]

        // Consider the last element of the desired result: flipudRecursive(m, k)[k-1] == m[k-1 - (k-1)] == m[0]
        // Consider the first element of the desired result: flipudRecursive(m, k)[0] == m[k-1 - 0] == m[k-1]

        // The construction `recResult + [m[k-1]]` was incorrect for the definition.
        // It should be `[m[k-1]] + recResult` if the `recResult` is for the shorter sequence `m[0...k-2]`
        // However, the current function means `m` is the *full* array, and `k` is the length of the prefix to consider.
        // So `flipudRecursive(m, k-1)` flips `m[0...k-2]` into `[m[k-2], m[k-3], ..., m[0]]`

        // Let's re-evaluate the original postcondition in the context of `k`:
        // `flipudRecursive(m, k)[i] == m[k - 1 - i]`
        // This means, the i-th element of the flipped sequence of length k is the (k-1-i)-th element of original m.

        // `flipudRecursive(m, k-1)` has elements `m[(k-1)-1-i]` for `0 <= i < k-1`.
        // So `recResult[i] == m[k-2-i]`.

        // If we want `flipudRecursive(m, k)[i] == m[k-1-i]`:
        // The last element `flipudRecursive(m, k)[k-1]` should be `m[k-1 - (k-1)] = m[0]`.
        // The first element `flipudRecursive(m, k)[0]` should be `m[k-1]`.

        // The current implementation `recResult + [m[k - 1]]` is almost doing:
        // `(m[k-2], m[k-3], ..., m[0]) + (m[k-1])` which becomes
        // `(m[k-2], m[k-3], ..., m[0], m[k-1])`.
        // This is not `(m[k-1], m[k-2], ..., m[0])`.

        // The `m[k-1]` being appended to the end actually needs to be `m[0]` from the perspective of the `k`th item.
        // If we expect `flipudRecursive(m, k)[k-1] == m[0]` based on the ensurs clause.
        // And if `recResult` already computes `flipudRecursive(m, k-1)`, its last element is `m[0]` using the index based on `k-1`.
        // What's failing is the assertion for the element `m[k-1]`. It corresponds to output `m[k-1 - (k-1)]` which is `m[0]`.
        // We are constructing a sequence of length k. `recResult` has length k-1.
        // The last element of `recResult` is `m[(k-1)-1-(k-2)] = m[0]`
        // If `recResult` correctly implements `m[k-2], m[k-3], ..., m[0]` then we just need to prepend `m[k-1]`.
        // So, `[m[k-1]] + recResult`

        // However, the `m[k-1]` in the argument of append is actually `m`'s index, not the value from the flipped original sequence.
        // Given `recResult[i] == m[k-2-i]` for `0 <= i < k-1`.
        // We want `result[i] == m[k-1-i]`.
        // For `i = 0`, `result[0] == m[k-1]`.
        // For `i > 0`, `result[i] == m[k-1-i]`. Let `j = i-1`. Then `result[j+1] == m[k-1-(j+1)] = m[k-2-j]`.
        // This is exactly `recResult[j]`.
        // So, the code should be `[m[k-1]] + recResult`.
        [m[k-1]] + recResult
    )
}

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calls the helper function flipudRecursive with the correct parameters. */
{
  result := flipudRecursive(m, |m|);
}
// </vc-code>
