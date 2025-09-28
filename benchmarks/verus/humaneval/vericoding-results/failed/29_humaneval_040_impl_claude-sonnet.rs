// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add proof that no triple exists when returning false */
    let n = l.len();
    for i in 0..n
        invariant
            n == l.len(),
    {
        for j in (i + 1)..n
            invariant
                n == l.len(),
                0 <= i < n,
        {
            for k in (j + 1)..n
                invariant
                    n == l.len(),
                    0 <= i < j < n,
            {
                let sum = l[i] as i32 + l[j] as i32 + l[k] as i32;
                if sum == 0 {
                    proof {
                        let mapped_seq = l@.map(|idx, x: i8| x as int);
                        assert(mapped_seq[i as int] == l@[i as int] as int);
                        assert(mapped_seq[j as int] == l@[j as int] as int);
                        assert(mapped_seq[k as int] == l@[k as int] as int);
                        assert(mapped_seq[i as int] + mapped_seq[j as int] + mapped_seq[k as int] == 0);
                        assert(has_triple_sum_to_zero(mapped_seq));
                    }
                    return true;
                }
            }
        }
    }
    proof {
        let mapped_seq = l@.map(|idx, x: i8| x as int);
        assert(forall|i: int, j: int, k: int| 0 <= i < j < k < mapped_seq.len() ==> mapped_seq[i] + mapped_seq[j] + mapped_seq[k] != 0);
        assert(!has_triple_sum_to_zero(mapped_seq));
    }
    false
}
// </vc-code>


}

fn main() {}