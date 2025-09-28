// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* code modified by LLM (iteration 5): fixed arithmetic overflow/underflow issues and improved bounds handling */
{
    let len = a.len();
    let mut sum: i64 = 0;
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            sum == vec_sum(a@.subrange(0, i as int)),
            sum >= (i as i64) * (i32::MIN as i64),
            sum <= (i as i64) * (i32::MAX as i64),
        decreases len - i
    {
        let current = a[i] as i64;
        proof {
            assert((i32::MIN as i64) <= current <= (i32::MAX as i64));
        }
        sum = sum + current;
        i = i + 1;
    }
    let len_i64 = len as i64;
    proof {
        assert(len_i64 > 0);
    }
    let result = (sum / len_i64) as i32;
    proof {
        assert((result as int) * (len as int) == vec_sum(a@));
        if all_equal(a@) {
            assert(result == a[0]);
        }
    }
    result
}
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

// </vc-code>


}
fn main() {}