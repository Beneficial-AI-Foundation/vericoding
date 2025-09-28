// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0
}

spec fn count_survivors(n: int, a: Seq<int>) -> int {
    count_survivors_from(n, a, 0, n)
}

spec fn count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> int
    decreases n - start
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives: int = if i < left { 1 } else { 0 };
        let new_left: int = if i - a[i] < left { i - a[i] } else { left };
        survives + count_survivors_from(n, a, start + 1, new_left)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added bounds checking lemma for array access */
lemma lemma_array_bounds(n: i8, a: Vec<i8>, i: i8)
    requires
        n >= 1,
        a@.len() == n,
        0 <= i < n
    ensures
        i as usize < a.len()
{
    assert(i as usize < n as usize);
    assert(n as usize == a.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed invariant and added bounds checks */
    let mut survivors = 0i8;
    let mut left = n;
    let mut i = n - 1;
    
    while i >= 0
        invariant
            left >= 0,
            left <= n,
            survivors >= 0,
            survivors <= n,
            i < n,
            survivors as int == count_survivors_from(n as int, a@.map_values(|x: i8| x as int), (n - i - 1) as int, left as int)
        decreases i
    {
        if i < left {
            survivors = survivors + 1;
        }
        
        assert(i >= 0);
        assert(i < n);
        lemma_array_bounds(n, a, i);
        
        let bullet_pos = if a[i as usize] <= i { i - a[i as usize] } else { 0 };
        if bullet_pos < left {
            left = bullet_pos;
        }
        
        i = i - 1;
    }
    
    survivors
}
// </vc-code>


}

fn main() {}