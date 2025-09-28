// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error in swap lemma path */
    let mut result = a;
    let len = result.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == len,
            a.len() == len,
            forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
            forall|j: int, k: int| 0 <= j < k < i ==> result[j] <= result[k],
            forall|j: int, k: int| (0 <= j < i && i <= k < len) ==> result[j] <= result[k],
        decreases len - i
    {
        let mut min_idx = i;
        let mut k = i + 1;
        while k < len
            invariant
                0 <= i < len,
                result.len() == len,
                a.len() == len,
                forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
                forall|j: int, l: int| 0 <= j < l < i ==> result[j] <= result[l],
                forall|j: int, l: int| (0 <= j < i && i <= l < len) ==> result[j] <= result[l],
                i < k <= len,
                i <= min_idx < len,
                forall|j: int| i <= j < k ==> result[min_idx] <= result[j],
            decreases len - k
        {
            if result[k] < result[min_idx] {
                min_idx = k;
            }
            k = k + 1;
        }

        assert(forall|j: int| i <= j < len ==> result[min_idx] <= result[j]);

        proof {
            vstd::seq::lemma_swap_preserves_multiset(result@, i as int, min_idx as int);
        }
        result.swap(i, min_idx);

        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}