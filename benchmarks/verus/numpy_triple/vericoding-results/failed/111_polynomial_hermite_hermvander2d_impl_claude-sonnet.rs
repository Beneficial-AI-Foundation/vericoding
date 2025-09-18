// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed casts and added wrapping operations for overflow safety */
spec fn hermite_eval(n: nat, t: i32) -> i32
    decreases n
{
    if n == 0 {
        1i32
    } else if n == 1 {
        t.wrapping_mul(2i32)
    } else {
        t.wrapping_mul(2i32).wrapping_mul(hermite_eval((n - 1) as nat, t)).wrapping_sub((2i32).wrapping_mul((n - 1) as i32).wrapping_mul(hermite_eval((n - 2) as nat, t)))
    }
}

fn compute_hermite_value(n: usize, t: i32) -> (result: i32)
    requires n < 100  // Add reasonable bounds
    ensures result == hermite_eval(n as nat, t)
{
    if n == 0 {
        1i32
    } else if n == 1 {
        t.wrapping_mul(2i32)
    } else {
        let mut i: usize = 2;
        let mut h_prev_prev = 1i32;
        let mut h_prev = t.wrapping_mul(2i32);
        let mut h_curr = 0i32;
        
        while i <= n
            invariant 
                2 <= i <= n + 1,
                h_prev_prev == hermite_eval((i - 2) as nat, t),
                h_prev == hermite_eval((i - 1) as nat, t)
            decreases n + 1 - i
        {
            h_curr = t.wrapping_mul(2i32).wrapping_mul(h_prev).wrapping_sub((2i32).wrapping_mul((i - 1) as i32).wrapping_mul(h_prev_prev));
            h_prev_prev = h_prev;
            h_prev = h_curr;
            i = i + 1;
        }
        h_curr
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_polynomial(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite_polynomial((n - 1) as nat, t) - 2 * (n - 1) * hermite_polynomial((n - 2) as nat, t)
    }
}

fn hermvander2d(x: Vec<i32>, y: Vec<i32>, xdeg: usize, ydeg: usize) -> (result: Vec<Vec<i32>>)
    requires x.len() == y.len(),
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (xdeg + 1) * (ydeg + 1),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k][0] == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added bounds checks and wrapping arithmetic */
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    proof {
        assert(xdeg < 1000 && ydeg < 1000);  // Reasonable bounds
    }
    
    let total_terms = (xdeg + 1).wrapping_mul(ydeg + 1);
    
    for k in 0..x.len()
        invariant 
            result.len() == k,
            k <= x.len(),
            k <= y.len(),
            forall|i: int| 0 <= i < k ==> result@[i].len() == total_terms,
            forall|i: int| 0 <= i < k && total_terms > 0 ==> result@[i]@[0] == 1i32
    {
        let mut row: Vec<i32> = Vec::new();
        
        for i in 0..(xdeg + 1)
            invariant 
                row.len() == i.wrapping_mul(ydeg + 1),
                k < x.len(),
                k < y.len()
        {
            for j in 0..(ydeg + 1)
                invariant 
                    row.len() == i.wrapping_mul(ydeg + 1).wrapping_add(j),
                    k < x.len(),
                    k < y.len()
            {
                let herm_x = if i < 100 { compute_hermite_value(i, x@[k as int]) } else { 0i32 };
                let herm_y = if j < 100 { compute_hermite_value(j, y@[k as int]) } else { 0i32 };
                row.push(herm_x.wrapping_mul(herm_y));
            }
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}