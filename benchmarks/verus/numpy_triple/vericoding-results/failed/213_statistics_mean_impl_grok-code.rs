// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] as int + vec_sum(a.skip(1))
    }
}

spec fn all_equal(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

fn mean(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures 
        /* Core property: mean * count == sum */
        (result as int) * (a.len() as int) == vec_sum(a@),
        /* For constant vectors, mean equals the constant */
        all_equal(a@) ==> result == a[0]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed variable declarations, used i64 for sum to handle larger sums, added loop invariant for proof, and assertions to satisfy ensures */
    let mut sum_i64: i64 = 0;
    for i in 0..a.len()
        invariant
            sum_i64 as int == vec_sum(a@.take(i as int)),
    {
        sum_i64 += a[i] as i64;
    }
    let len = a.len() as i64;
    let result = (sum_i64 / len) as i32;
    proof {
        assert(sum_i64 as int == vec_sum(a@));
        assert((result as int) * (a.len() as int) == sum_i64 as int);
    }
}
// </vc-code>


}
fn main() {}