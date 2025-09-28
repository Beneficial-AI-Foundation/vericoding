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
proof fn peek_sum_step(v: &Vec<i32>, i: int)
    requires 0 <= i < v.len()
    ensures peek_sum(v, (i + 1) as int) == 
        if is_peek(v, i) { 
            v[i] + peek_sum(v, i) 
        } else { 
            peek_sum(v, i) 
        }
{
    assert(peek_sum(v, (i + 1) as int) == 
        if is_peek(v, i) { 
            v[i] + peek_sum(v, i) 
        } else { 
            peek_sum(v, i) 
        });
}

proof fn is_peek_max_property(v: &Vec<i32>, i: int, max: i32)
    requires 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < i ==> v[k] <= max,
        v[i] >= max
    ensures is_peek(v, i)
{
    assert forall|k: int| 0 <= k < i implies #[trigger] v[i] >= v[k] by {
        assert(v[k] <= max);
        assert(v[i] >= max);
    }
}

proof fn not_peek_max_property(v: &Vec<i32>, i: int, max: i32)
    requires 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < i ==> v[k] <= max,
        exists|j: int| 0 <= j < i && v[j] == max,
        v[i] < max
    ensures !is_peek(v, i)
{
    let j = choose|j: int| 0 <= j < i && v[j] == max;
    assert(v[i] < v[j]);
}

proof fn is_peek_at_zero(v: &Vec<i32>)
    requires v.len() > 0
    ensures is_peek(v, 0)
{
    // For i = 0, the condition 0 <= k < 0 is vacuously true
    // since there are no such k values
    assert(is_peek(v, 0));
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
    let mut max: i32 = v[0];
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peek_sum(v, i as int),
            i > 0 ==> forall|k: int| 0 <= k < i ==> v[k] <= max,
            i > 0 ==> exists|j: int| 0 <= j < i && v[j] == max
        decreases v.len() - i
    {
        if i == 0 {
            proof {
                is_peek_at_zero(v);
                peek_sum_step(v, 0);
            }
            sum = sum + v[0];
            max = v[0];
        } else {
            if v[i] >= max {
                proof {
                    is_peek_max_property(v, i as int, max);
                    peek_sum_step(v, i as int);
                }
                sum = sum + v[i];
                max = v[i];
            } else {
                proof {
                    not_peek_max_property(v, i as int, max);
                    peek_sum_step(v, i as int);
                }
            }
        }
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}