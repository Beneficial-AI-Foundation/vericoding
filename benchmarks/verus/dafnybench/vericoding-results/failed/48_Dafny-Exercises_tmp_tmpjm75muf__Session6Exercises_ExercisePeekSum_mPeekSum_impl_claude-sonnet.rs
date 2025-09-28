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
proof fn lemma_peek_sum_monotonic(v: &Vec<i32>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures peek_sum(v, i) <= peek_sum(v, j)
    decreases j - i
{
    if i == j {
        return;
    }
    lemma_peek_sum_monotonic(v, i, j - 1);
}

proof fn lemma_peek_sum_extend(v: &Vec<i32>, i: int)
    requires 0 <= i < v.len()
    ensures peek_sum(v, i + 1) == peek_sum(v, i) + if is_peek(v, i) { v[i] } else { 0 }
{
}

spec fn seq_max(s: Seq<i32>) -> i32
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = seq_max(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
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
    let mut sum: i32 = 0;
    let mut max_so_far: i32 = i32::MIN;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            sum == peek_sum(v, i as int),
            i > 0 ==> max_so_far == seq_max(v@.subrange(0, i as int))
        decreases v.len() - i
    {
        let current = v[i];
        let is_current_peek = if i == 0 {
            true
        } else {
            current >= max_so_far
        };
        
        if is_current_peek {
            proof {
                if i == 0 {
                    assert(forall|k: int| 0 <= k < 0 ==> v[0] >= #[trigger] v[k]);
                    assert(is_peek(v, 0));
                } else {
                    assert(current >= max_so_far);
                    assert(forall|k: int| 0 <= k < i ==> #[trigger] v[k as int] <= max_so_far);
                    assert(forall|k: int| 0 <= k < i ==> current >= #[trigger] v[k as int]);
                    assert(is_peek(v, i as int));
                }
            }
            sum = sum + current;
        }
        
        if i == 0 {
            max_so_far = current;
        } else {
            max_so_far = if current > max_so_far { current } else { max_so_far };
        }
        
        proof {
            lemma_peek_sum_extend(v, i as int);
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}