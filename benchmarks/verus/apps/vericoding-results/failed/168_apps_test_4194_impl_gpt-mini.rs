// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n >= 0 && m >= 0 && m == a.len()
}

spec fn can_complete_all_assignments(n: int, a: Seq<int>) -> bool {
    sum_seq(a) <= n
}

spec fn total_assignment_days(a: Seq<int>) -> int {
    sum_seq(a)
}

spec fn sum_seq(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): computes prefix sum of first k elements of a Vec<i8> */
spec fn vec_prefix_sum(a: Vec<i8>, k: int) -> int
    decreases
        k
{
    if k <= 0 {
        0
    } else if k <= a.len() as int {
        vec_prefix_sum(a, k - 1) + (a@)[k - 1] as int
    } else {
        vec_prefix_sum(a, a.len() as int)
    }
}

/* helper modified by LLM (iteration 5): proves vec_prefix_sum equals sum_seq of mapped subrange */
proof fn prefix_sum_matches_seq(a: Vec<i8>, k: int)
    requires
        0 <= k && k <= a.len() as int,
    ensures
        vec_prefix_sum(a, k) == sum_seq(a@.map(|i, x: i8| x as int).subrange(0, k)),
    decreases
        k
{
    if k == 0 {
        assert(vec_prefix_sum(a, 0) == 0);
        assert(sum_seq(a@.map(|i, x: i8| x as int).subrange(0, 0)) == 0);
    } else {
        prefix_sum_matches_seq(a, k - 1);
        assert(vec_prefix_sum(a, k) == vec_prefix_sum(a, k - 1) + (a@)[k - 1] as int);
        assert(sum_seq(a@.map(|i, x: i8| x as int).subrange(0, k)) == sum_seq(a@.map(|i, x: i8| x as int).subrange(0, k - 1)) + (a@.map(|i, x: i8| x as int))[k - 1]);
        assert((a@.map(|i, x: i8| x as int))[k - 1] == (a@)[k - 1] as int);
        assert(vec_prefix_sum(a, k - 1) == sum_seq(a@.map(|i, x: i8| x as int).subrange(0, k - 1)));
        assert(vec_prefix_sum(a, k) == sum_seq(a@.map(|i, x: i8| x as int).subrange(0, k)));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x: i8| x as int))
    ensures 
        m as int == 0 ==> result as int == n as int,
        m as int > 0 && can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == n as int - total_assignment_days(a@.map(|i, x: i8| x as int)),
        m as int > 0 && !can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == -1,
        result as int >= -1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute total using runtime types and maintain ghost invariant relating to vec_prefix_sum */
{
    // impl-start
    let len: usize = a.len();
    let mut i: usize = 0;
    let mut total: i32 = 0;
    while i < len
        invariant
            i <= len,
            total as int == vec_prefix_sum(a, i as int),
        decreases
            len - i
    {
        let x: i32 = a[i] as i32;
        let new_total: i32 = total + x;
        proof {
            assert(0 <= i as int);
            assert(i as int <= a.len() as int);
            assert(total as int == vec_prefix_sum(a, i as int));
            prefix_sum_matches_seq(a, i as int);
            assert(vec_prefix_sum(a, (i as int) + 1) == vec_prefix_sum(a, i as int) + (a@)[i as int] as int);
            assert((a@.map(|j, y: i8| y as int))[i as int] == (a@)[i as int] as int);
            assert(new_total as int == vec_prefix_sum(a, (i as int) + 1));
        }
        total = new_total;
        i = i + 1;
    }

    let result: i8 = if m == 0 {
        n
    } else if total <= n as i32 {
        (n as i32 - total) as i8
    } else {
        -1
    };
    result
    // impl-end
}

// </vc-code>


}

fn main() {}