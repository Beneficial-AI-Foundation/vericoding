// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
{
    /* helper modified by LLM (iteration 5): lemma connecting Vec length (usize) to view().len() (int) for use in indexing proofs */
    proof fn len_usize_to_int(v: &Vec<char>)
        ensures
            (v.len() as int) == v.view().len(),
    {
        proof {
            assert((v.len() as int) == v.view().len());
        }
    }
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
    /* code modified by LLM (iteration 5): run-length encoding with strengthened invariants to ensure indexing and element properties */
    let mut result: Vec<(char, usize)> = Vec::new();
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].1 > 0,
            forall|k: int| 0 <= k < result.len() ==> k + 1 < result.len() ==> #[trigger] result[k].0 != result[k + 1].0,
        decreases n - i
    {
        let c = s[i];
        let mut j: usize = i + 1;
        while j < n && s[j] == c
            invariant
                i <= j,
                j <= n,
                forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].1 > 0,
                forall|k: int| 0 <= k < result.len() ==> k + 1 < result.len() ==> #[trigger] result[k].0 != result[k + 1].0,
            decreases n - j
        {
            j += 1;
        }
        let count: usize = j - i;
        // count > 0 because j >= i + 1
        result.push((c, count));
        i = j;
    }
    result
}
// </vc-code>

}
fn main() {}