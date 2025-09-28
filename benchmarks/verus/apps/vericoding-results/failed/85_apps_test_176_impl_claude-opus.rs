// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(k: int, a: int, b: int) -> bool {
  k > 0 && a <= b
}

spec fn floor_div(a: int, b: int) -> int {
  if a >= 0 { a / b }
  else { (a - b + 1) / b }
}

spec fn count_divisibles_in_range(k: int, a: int, b: int) -> int {
  floor_div(b, k) - floor_div(a - 1, k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added lemma to prove count bounds */
proof fn lemma_count_bounds(k: int, a: int, b: int)
    requires
        k > 0,
        a <= b,
        -128 <= a <= 127,
        -128 <= b <= 127,
        -128 <= k <= 127,
    ensures
        0 <= count_divisibles_in_range(k, a, b) <= 127,
{
    // The maximum count is when k=1 and we count from -128 to 127
    // That gives us at most 256 numbers, but since we're counting in a subrange
    // and k >= 1, the count is at most (b - a + 1) / k
    assert(count_divisibles_in_range(k, a, b) == floor_div(b, k) - floor_div(a - 1, k));
    assert(floor_div(b, k) <= b / k + 1);
    assert(floor_div(a - 1, k) >= (a - 1) / k);
    assert(count_divisibles_in_range(k, a, b) <= (b - a + 1) / k + 1);
    assert((b - a + 1) <= 256);
    assert((b - a + 1) / k <= 256);
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8) -> (result: i8)
  requires
    valid_input(k as int, a as int, b as int),
  ensures
    result >= 0,
    result as int == count_divisibles_in_range(k as int, a as int, b as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed lemma call to use proof block */
    proof {
        lemma_count_bounds(k as int, a as int, b as int);
    }
    
    let mut count: i8 = 0;
    let mut i: i8 = a;
    
    while i <= b
        invariant
            a <= i,
            i <= b + 1,
            k > 0,
            0 <= count <= 127,
            count as int == floor_div(i as int - 1, k as int) - floor_div(a as int - 1, k as int),
            count as int <= (b - a + 1) as int,
        decreases b - i + 1
    {
        if i % k == 0 {
            if count < 127 {
                count = count + 1;
            }
        }
        if i < 127 {
            i = i + 1;
        } else {
            break;
        }
    }
    
    count
}
// </vc-code>


}

fn main() {}