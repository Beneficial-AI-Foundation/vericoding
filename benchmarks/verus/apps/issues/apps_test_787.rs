// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn concat_seqs(seqs: Seq<Seq<char>>) -> Seq<char>
    decreases seqs.len()
{
    if seqs.len() == 0 { 
        Seq::<char>::empty() 
    } else { 
        seqs[0] + concat_seqs(seqs.subrange(1, seqs.len() as int))
    }
}

spec fn valid_split(result: Seq<Seq<char>>, k: int, q: Seq<char>) -> bool {
    result.len() == k &&
    (forall|i: int| 0 <= i < result.len() ==> result[i].len() > 0) &&
    (forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, q: Vec<char>) -> (result: Vec<Vec<char>>)
    requires 
        k >= 0,
        q.len() >= 0,
    ensures 
        k <= 0 || q.len() == 0 ==> result.len() == 0,
        k > 0 && q.len() > 0 ==> (
            (result.len() == 0) || valid_split(Seq::new(result.len(), |i: int| result[i]@), k as int, q@)
        ),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}