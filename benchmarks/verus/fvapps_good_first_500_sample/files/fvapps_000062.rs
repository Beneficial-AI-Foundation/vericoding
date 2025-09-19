// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_sum(v: Seq<usize>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] as int + vec_sum(v.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
spec fn solve_spec(n: usize, k: usize, nums: Seq<i64>, friends: Seq<usize>) -> i64;

fn solve(n: usize, k: usize, nums: Vec<i64>, friends: Vec<usize>) -> (result: i64)
    requires 
        k >= 1,
        n >= k,
        nums.len() == n,
        friends.len() == k,
        vec_sum(friends@) == n as int,
        forall|i: int| 0 <= i < friends.len() ==> friends[i] >= 1,
    ensures
        result == solve_spec(n, k, nums@, friends@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

proof fn solve_case1() {
    assume(solve_spec(4, 2, seq![1, 13, 7, 17], seq![1, 3]) == 48);
}

proof fn solve_case2() {
    assume(solve_spec(6, 2, seq![10, 10, 10, 10, 11, 11], seq![3, 3]) == 42);
}

proof fn solve_case3() {
    assume(solve_spec(4, 4, seq![1000000000, 1000000000, 1000000000, 1000000000], seq![1, 1, 1, 1]) == 8000000000);
}
// </vc-code>


}

fn main() {}