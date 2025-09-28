// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vec_sum_take_lemma(a: Seq<i32>, i: int)
    requires 0 <= i <= a.len()
    ensures i == a.len() ==> vec_sum(a.take(i)) == vec_sum(a)
{
    if i == a.len() {
        assert(a.take(i) =~= a);
    }
}

proof fn vec_sum_take_step(a: Seq<i32>, i: int)
    requires 0 <= i < a.len()
    ensures vec_sum(a.take((i + 1) as int)) == vec_sum(a.take(i as int)) + (a[i] as int)
{
    let take_i = a.take(i as int);
    let take_i_plus_1 = a.take((i + 1) as int);
    assert(take_i_plus_1.len() == i + 1);
    assert(take_i_plus_1[i] == a[i]);
    assert(take_i_plus_1.take(i as int) =~= take_i);
}

/* helper modified by LLM (iteration 5): Fixed all_equal call to remove @*/ 
proof fn all_equal_vec_sum(a: Seq<i32>)
    requires a.len() > 0, all_equal(a)
    ensures vec_sum(a) == (a[0] as int) * (a.len() as int)
    decreases a.len()
{
    if a.len() == 1 {
        assert(vec_sum(a) == a[0] as int);
    } else {
        assert(a[0] == a[1]);
        all_equal_vec_sum(a.skip(1));
        assert(vec_sum(a.skip(1)) == (a[1] as int) * ((a.len() - 1) as int));
        assert(vec_sum(a) == (a[0] as int) + vec_sum(a.skip(1)));
    }
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
{
    /* code modified by LLM (iteration 5): Fix overflow and division precision issues */
    let mut sum: i64 = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == vec_sum(a@.take(i as int)),
            sum <= i64::MAX / 2,
        decreases a.len() - i
    {
        proof {
            vec_sum_take_step(a@, i as int);
        }
        sum = sum + a[i] as i64;
        i = i + 1;
    }
    
    proof {
        vec_sum_take_lemma(a@, i as int);
        assert(sum == vec_sum(a@));
    }
    
    let len_i64 = a.len() as i64;
    let result = (sum / len_i64) as i32;
    
    proof {
        if all_equal(a@) {
            all_equal_vec_sum(a@);
            assert(vec_sum(a@) == (a[0] as int) * (a.len() as int));
            assert(sum == (a[0] as int) * (a.len() as int));
            assert(sum / len_i64 == a[0] as i64);
            assert(result == a[0]);
        }
        assert((result as int) * (a.len() as int) == sum - (sum % len_i64));
        assert((result as int) * (a.len() as int) <= vec_sum(a@));
        assert((result as int) * (a.len() as int) + (a.len() as int) > vec_sum(a@));
    }
    
    result
}
// </vc-code>


}
fn main() {}