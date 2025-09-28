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

proof fn count_survivors_from_decreases(n: int, a: Seq<int>, start: int, left: int)
    requires
        start < n,
        n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0,
    ensures
        n - (start + 1) < n - start,
{
}

spec fn next_left(current_left: int, pos: int, jump: int) -> int {
    let proposed = pos - jump;
    if proposed < current_left {
        proposed
    } else {
        current_left
    }
}

/* helper modified by LLM (iteration 5): Fixed invariant_maintained to use ghost parameters */
proof fn invariant_maintained(n: int, a: Seq<int>, i: int, current_left: int, result: int)
    requires
        n >= 1 && a.len() == n && forall|k: int| 0 <= k < n ==> a[k] >= 0,
        0 <= i <= n,
        current_left >= 0 && current_left <= n,
    ensures
        result == count_survivors_from(n, a, n - i, current_left),
{
    if i == 0 {
        assert(result == count_survivors_from(n, a, n, current_left));
    } else {
        let prev_i = i - 1;
        let pos = n - i;
        let jump = a[pos];
        let survives = if pos < current_left { 1 } else { 0 };
        let new_left = next_left(current_left, pos, jump);
        
        invariant_maintained(n, a, prev_i, new_left, result - survives);
        
        assert(result == survives + count_survivors_from(n, a, n - prev_i, new_left));
        assert(count_survivors_from(n, a, n - i, current_left) == survives + count_survivors_from(n, a, n - prev_i, new_left));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost conversions for invariant_maintained call */
    let mut result: i8 = 0;
    let mut current_left = n;
    
    let mut i: i8 = n - 1;
    
    while i >= 0
        invariant
            i >= -1 && i <= n - 1,
            result >= 0 && result <= n,
            current_left >= 0 && current_left <= n,
            result as int == count_survivors_from(n as int, a@.map_values(|x: i8| x as int), n as int - i as int - 1, current_left as int),
        decreases i as int + 1
    {
        let pos = i;
        let jump = a[pos as usize];
        
        if pos < current_left {
            result = (result + 1) as i8;
        }
        
        let proposed = pos - jump;
        if proposed < 0 {
            current_left = 0;
        } else if proposed < current_left {
            current_left = proposed;
        }
        
        proof {
            let ghost_n: int = n as int;
            let ghost_a: Seq<int> = a@.map_values(|x: i8| x as int);
            let ghost_i: int = (n as int - i as int - 1) as int;
            let ghost_current_left: int = current_left as int;
            let ghost_result: int = result as int;
            invariant_maintained(ghost_n, ghost_a, ghost_i, ghost_current_left, ghost_result);
        }
        
        i = i - 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}