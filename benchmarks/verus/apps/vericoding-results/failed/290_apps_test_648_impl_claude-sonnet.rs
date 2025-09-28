// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(m: int, b: int) -> bool {
  1 <= m <= 1000 && 1 <= b <= 10000
}

spec fn f(x: int, y: int) -> int {
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

spec fn valid_rectangle_corner(k: int, m: int, b: int) -> bool {
  0 <= k && b - k >= 0
}

spec fn rectangle_value(k: int, m: int, b: int) -> int {
  f(k * m, b - k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures clauses to use return values correctly */
exec fn compute_f(x: i32, y: i32) -> (result: i32)
    requires
        x >= 0,
        y >= 0,
        x <= 1000000,
        y <= 10000
    ensures
        result == f(x as int, y as int)
{
    (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

exec fn compute_rectangle_value(k: i32, m: i32, b: i32) -> (result: i32)
    requires
        0 <= k,
        b - k >= 0,
        m >= 1,
        k <= 10000,
        m <= 1000,
        b <= 10000
    ensures
        result == rectangle_value(k as int, m as int, b as int)
{
    compute_f(k * m, b - k)
}

proof fn lemma_f_monotonic(x1: int, y1: int, x2: int, y2: int)
    requires
        x1 <= x2,
        y1 <= y2,
        x1 >= 0,
        y1 >= 0
    ensures
        f(x1, y1) <= f(x2, y2)
{
}

proof fn lemma_rectangle_value_bounds(k: int, m: int, b: int)
    requires
        valid_rectangle_corner(k, m, b),
        valid_input(m, b),
        m >= 1
    ensures
        rectangle_value(k, m, b) <= 127
{
}

proof fn lemma_search_correctness(m: int, b: int, best_k: int, best_val: int)
    requires
        valid_input(m, b),
        valid_rectangle_corner(best_k, m, b),
        best_val == rectangle_value(best_k, m, b),
        forall|k: int| 0 <= k <= b ==> rectangle_value(k, m, b) <= best_val
    ensures
        forall|k: int| valid_rectangle_corner(k, m, b) ==> best_val >= rectangle_value(k, m, b),
        exists|k: int| valid_rectangle_corner(k, m, b) && best_val == rectangle_value(k, m, b)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(m: i8, b: i8) -> (result: i8)
  requires 
    valid_input(m as int, b as int)
  ensures 
    result as int >= -1,
    forall|k: int| valid_rectangle_corner(k, m as int, b as int) ==> result as int >= rectangle_value(k, m as int, b as int),
    exists|k: int| valid_rectangle_corner(k, m as int, b as int) && result as int == rectangle_value(k, m as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut best_k: i32 = 0;
    let mut best_val: i32 = compute_rectangle_value(0, m as i32, b as i32);
    let mut k: i32 = 1;
    
    while k <= b as i32
        invariant
            0 <= k <= b as i32 + 1,
            valid_rectangle_corner(best_k as int, m as int, b as int),
            best_val as int == rectangle_value(best_k as int, m as int, b as int),
            forall|j: int| 0 <= j < k ==> rectangle_value(j, m as int, b as int) <= best_val as int
        decreases b as i32 + 1 - k
    {
        let current_val = compute_rectangle_value(k, m as i32, b as i32);
        
        if current_val > best_val {
            best_k = k;
            best_val = current_val;
        }
        
        k = k + 1;
    }
    
    proof {
        lemma_search_correctness(m as int, b as int, best_k as int, best_val as int);
    }
    
    best_val as i8
}
// </vc-code>


}

fn main() {}