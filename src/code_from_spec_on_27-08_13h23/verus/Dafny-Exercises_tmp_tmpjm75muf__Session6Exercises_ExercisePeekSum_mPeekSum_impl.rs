use vstd::prelude::*;

verus! {

spec fn is_peek(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

spec fn peek_sum(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i when 0 <= i <= v.len()
{
    if i == 0 {
        0
    } else {
        if is_peek(v, i - 1) {
            v[i - 1] + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        }
    }
}

// <vc-helpers>
proof fn lemma_peek_sum_monotonic(v: &Vec<i32>, i: int)
    requires 0 <= i <= v.len()
    ensures forall|j: int| 0 <= j <= i ==> peek_sum(v, j) <= peek_sum(v, i)
    decreases i
{
    if i > 0 {
        lemma_peek_sum_monotonic(v, i - 1);
        if is_peek(v, i - 1) {
            assert(peek_sum(v, i) == v[i - 1] + peek_sum(v, i - 1));
            assert forall|j: int| 0 <= j <= i - 1 implies peek_sum(v, j) <= peek_sum(v, i - 1) by {
                assert(peek_sum(v, j) <= peek_sum(v, i - 1));
            };
            assert(peek_sum(v, i - 1) <= peek_sum(v, i));
        } else {
            assert(peek_sum(v, i) == peek_sum(v, i - 1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
    //Implement and verify an O(v.len()) algorithm to solve this problem
// </vc-spec>
// </vc-spec>

// <vc-code>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peek_sum(v, i as int)
    {
        if i > 0 && is_peek(v, (i - 1) as int) {
            sum = sum + v[i - 1];
        }
        i = i + 1;
    }
    proof {
        lemma_peek_sum_monotonic(v, v.len() as int);
    }
    sum
}
// </vc-code>

fn main() {}

}