use vstd::prelude::*;

verus! {

// Given an array of integers, it returns the sum. [1,3,3,2]->9

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

// <vc-helpers>
proof fn lemma_sum_take(s: Seq<i32>, n: int)
    requires 0 <= n < s.len()
    ensures sum(s.take(n+1)) == sum(s.take(n)) + s[n] as int
{
    let s_prime = s.take(n+1);
    assert(s_prime.len() == n+1);
    assert(s_prime.subrange(0, s_prime.len() - 1) == s.take(n));
    assert(s_prime[s_prime.len() - 1] == s[n]);
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let ghost total_int = 0;
    let mut total: i128 = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            total_int == sum(xs@.take(i as int)),
            total as int == total_int,
        decreases xs.len() - i
    {
        let x = xs[i] as i128;
        total = total + x;
        total_int = total_int + xs[i] as int;
        i = i + 1;
        proof {
            lemma_sum_take(xs@, (i - 1) as int);
        }
    }
    assert(total_int >= i32::MIN as int && total_int <= i32::MAX as int);
    total as i32
}
// </vc-code>

fn main() {
}

}