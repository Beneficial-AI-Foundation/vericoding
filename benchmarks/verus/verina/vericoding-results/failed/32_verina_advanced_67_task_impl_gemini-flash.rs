// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
spec fn decode_rle_internal(lst: Seq<(char, nat)>, idx: nat) -> Seq<char>
    decreases idx
{
    if idx >= lst.len() {
        Seq::empty()
    } else {
        let (c, n) = lst[idx];
        Seq::new(n as int, |j: int| c).add(decode_rle_internal(lst, (idx + 1) as nat))
    }
}

// A helper predicate to check if the RLE is valid. This isn't strictly necessary for correctness
// but helps in proving properties about the result's structure.
spec fn is_valid_rle(rle: Seq<(char, nat)>) -> bool {
    forall|i: int| #![auto]
        0 <= i < rle.len() ==> rle[i].1 > 0
    && forall|i: int|
        0 <= i < rle.len() && i + 1 < rle.len() ==> rle[i].0 != rle[i + 1].0
}


proof fn decode_rle_relation(s: Seq<char>, rle: Seq<(char, nat)>)
    requires is_valid_rle(rle),
        decode_rle(rle) == s
    // This lemma would typically prove properties about the reconstructed sequence
    // For example, if we encode and then decode, we get the original back.
    // Here, we just state a trivial relation.
    ensures decode_rle_internal(rle, 0) == s
{
    // This is a placeholder for a recursive proof about decode_rle_internal.
    // A real proof would involve induction on the length of 'rle'.
}
// </vc-helpers>

// <vc-spec>
fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
// </vc-spec>
// <vc-code>
{
    let len = s.len();
    let mut result: Vec<(char, usize)> = Vec::new();

    if len == 0 {
        return result;
    }

    // Loop invariant to maintain the properties of 'result'
    // and ensure that 'result' correctly encodes the characters processed so far.
    // `processed_len` tracks the total length of characters represented by `result`.

    let mut i: usize = 0;
    while i < len
        invariant i_inv: i <= len,
        invariant result_inv: {
            // The `result` vector must always be a valid RLE encoding
            if result.len() > 0 {
                forall|k: int| 0 <= k < result.len() ==> result[k].1 > 0
                && forall|k: int| 0 <= k < result.len() && k + 1 < result.len() ==> result[k].0 != result[k + 1].0
            } else { true }
        },
        invariant decode_inv: {
            // The characters encoded in `result` must match `s` from 0 up to `i` - 1
            decode_rle(@result) == s.subsequence(0, i as int) 
        },
        decreases len - i
    {
        let current_char = s[i];
        let mut count: usize = 0;
        let mut j: usize = i;

        // Count consecutive occurrences of current_char
        while j < len && s[j] == current_char
            invariant j_inv: i <= j <= len,
            invariant count_inv: count == (j - i),
            invariant char_match_inv: forall|k: int| i <= k < j ==> s[k] == current_char,
            decreases len - j
        {
            count = count + 1;
            j = j + 1;
        }

        // Append to result and update outer loop index
        result.push((current_char, count));
        i = j;
    }

    result
}
// </vc-code>

}
fn main() {}