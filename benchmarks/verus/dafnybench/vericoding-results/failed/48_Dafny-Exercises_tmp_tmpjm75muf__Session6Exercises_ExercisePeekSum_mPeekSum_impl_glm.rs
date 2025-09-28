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
spec fn max_of(v: &Vec<i32>, i: int) -> i32
    recommends 1 <= i <= v.len()
    decreases i
{
    if i == 1 {
        v@[0]
    } else {
        let m = max_of(v, i-1);
        if m > v@[i-1] { m } else { v@[i-1] }
    }
}
// </vc-helpers>

// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
    //Implement and verify an O(v.len()) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
    let mut sum = v[0];
    let mut max_so_far = v[0];
    let mut i: usize = 1;
    while i < v.len()
        decreases v.len() - i
        invariant 
            1 <= i as int <= v.len() as int,
            sum == peek_sum(v, i as int),
            max_so_far == max_of(v, i as int)
    {
        let idx = i;
        if v[idx] >= max_so_far {
            sum = sum + v[idx];
            max_so_far = v[idx];
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {}

}