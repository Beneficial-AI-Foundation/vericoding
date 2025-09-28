// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n
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

spec fn correct_result(n: int, arr: Seq<int>, result: int) -> bool {
    &&& (sum_seq(arr) % n == 0 ==> result == n)
    &&& (sum_seq(arr) % n != 0 ==> result == n - 1)
    &&& (result == n || result == n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sum_vec_range initialization and equivalence proofs */
proof fn sum_seq_vec_equiv(arr: Vec<i8>)
    ensures sum_seq(arr@.map(|i: int, x: i8| x as int)) == sum_vec(arr@)
{
    let mapped = arr@.map(|i: int, x: i8| x as int);
    sum_seq_vec_equiv_helper(arr@, mapped, 0);
    assert(sum_seq(mapped) == sum_vec_range(arr@, 0));
    assert(sum_vec(arr@) == sum_vec_range(arr@, 0));
}

proof fn sum_seq_vec_equiv_helper(orig: Seq<i8>, mapped: Seq<int>, start: int)
    requires
        start >= 0,
        start <= orig.len(),
        mapped == orig.map(|i: int, x: i8| x as int),
    ensures sum_seq(mapped.subrange(start, mapped.len() as int)) == sum_vec_range(orig, start)
    decreases orig.len() - start
{
    if start == orig.len() {
        assert(mapped.subrange(start, mapped.len() as int).len() == 0);
        assert(sum_seq(mapped.subrange(start, mapped.len() as int)) == 0);
        assert(sum_vec_range(orig, start) == 0);
    } else {
        let sub = mapped.subrange(start, mapped.len() as int);
        assert(sub[0] == mapped[start]);
        assert(mapped[start] == orig[start] as int);
        sum_seq_vec_equiv_helper(orig, mapped, start + 1);
        assert(sum_seq(sub.subrange(1, sub.len() as int)) == sum_vec_range(orig, start + 1));
        assert(sum_seq(sub) == sub[0] + sum_seq(sub.subrange(1, sub.len() as int)));
        assert(sum_seq(sub) == orig[start] as int + sum_vec_range(orig, start + 1));
        assert(sum_vec_range(orig, start) == orig[start] as int + sum_vec_range(orig, start + 1));
    }
}

spec fn sum_vec(arr: Seq<i8>) -> int
{
    sum_vec_range(arr, 0)
}

spec fn sum_vec_range(arr: Seq<i8>, start: int) -> int
    decreases if start >= 0 && start <= arr.len() { arr.len() - start } else { 0 }
{
    if start >= 0 && start < arr.len() {
        arr[start] as int + sum_vec_range(arr, start + 1)
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant initialization and simplified proof */
    let mut sum: i64 = 0;
    let mut i = 0;
    
    assert(sum_vec_range(arr@, 0) == sum_vec(arr@));
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum == sum_vec_range(arr@, 0) - sum_vec_range(arr@, i as int),
        decreases arr.len() - i
    {
        sum = sum + (arr[i] as i64);
        i = i + 1;
    }
    
    proof {
        sum_seq_vec_equiv(arr);
        assert(sum == sum_vec(arr@) as i64);
        assert(sum == sum_seq(arr@.map(|i: int, x: i8| x as int)) as i64);
    }
    
    let remainder = sum % (n as i64);
    
    if remainder == 0 {
        n
    } else {
        n - 1
    }
}
// </vc-code>


}

fn main() {}