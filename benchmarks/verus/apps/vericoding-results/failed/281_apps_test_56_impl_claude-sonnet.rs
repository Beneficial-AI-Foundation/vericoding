// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, t: int) -> bool {
    1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
    n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
    result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
    (t == 0 ==> result == 0) &&
    (n == 1 && t >= 1 ==> result == 1) &&
    (n == 1 && t == 0 ==> result == 0) &&
    (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>
spec fn glasses_in_row(row: int) -> int {
    row
}

spec fn glasses_up_to_row(row: int) -> int {
    row * (row + 1) / 2
}

/* helper modified by LLM (iteration 5): fixed lemma keyword declaration syntax */
proof fn lemma_glasses_up_to_row(row: int)
    requires row >= 0
    ensures glasses_up_to_row(row) == row * (row + 1) / 2
{
}

proof fn lemma_total_glasses_is_triangle(n: int)
    requires n >= 1
    ensures total_glasses(n) == glasses_up_to_row(n)
{
}

spec fn can_fill_glasses(n: int, t: int, filled: int) -> bool {
    filled <= total_glasses(n) && filled <= t
}

fn calculate_total_glasses(n: i8) -> (result: i8)
    requires 1 <= n <= 10
    ensures result as int == total_glasses(n as int)
{
    proof {
        let ghost_total = total_glasses(n as int);
    }
    
    let mut total: i8 = 0;
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total as int == (i - 1) * i / 2
    {
        total = total + i;
        i = i + 1;
    }
    
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, t: i8) -> (result: i8)
requires 
    valid_input(n as int, t as int)
ensures 
    valid_result(result as int, n as int, t as int),
    correct_for_edge_cases(result as int, n as int, t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed cast to int in exec context */
    if t == 0 {
        return 0;
    }
    
    let total = calculate_total_glasses(n);
    
    if t >= total {
        return total;
    } else {
        return t;
    }
}
// </vc-code>


}

fn main() {}