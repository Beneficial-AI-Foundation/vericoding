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
spec fn get_max(v: Seq<i32>, a: int, b: int) -> i32
    requires 0 <= a <= b <= v.len()
{
    v@[a..b].fold_left(v@[a], |acc, x| if acc > x { acc } else { x })
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
    proof {
        assert(0 == peek_sum(v, 0));
        assert(v@[0] == peek_sum(v, 1));
    }
    let mut sum = v[0];
    let mut current_max = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            sum as int == peek_sum(v, i as int),
            current_max == get_max(v@, 0, i as int),
        decreases v.len() - i
    {
        if v[i] >= current_max {
            sum += v[i];
            current_max = v[i];
        }
        proof {
            let i_int = i as int;
            if v[i] >= current_max {
                assert (forall |k: int| 0 <= k < i_int ==> v@[k] <= current_max );
                assert (v[i] >= current_max);
                assert (forall |k: int| 0 <= k < i_int ==> v[i] >= v@[k]);
                assert (is_peek(v, i_int));
                assert (peek_sum(v, i_int + 1) == v[i] + peek_sum(v, i_int));
            } else {} 
            assert(sum as int == peek_sum(v, (i + 1) as int));
        }
        i += 1;
    }
    proof {
        assert(sum as int == peek_sum(v, v.len() as int));
    }
    sum
}
// </vc-code>

fn main() {}

}