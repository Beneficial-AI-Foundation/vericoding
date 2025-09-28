// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_less_value(n: int, m: int, target: int) -> int
  decreases n
{
  if n <= 0 {
    0
  } else {
    let max_j = (target - 1) / n;
    let actual_max_j = if max_j > m { m } else { max_j };
    let contribution = if actual_max_j >= 1 { actual_max_j } else { 0 };
    contribution + count_less_value(n - 1, m, target)
  }
}

spec fn count_less_or_equal_value(n: int, m: int, target: int) -> int {
  if target <= 0 {
    0
  } else if target >= n * m {
    n * m
  } else {
    count_less_value(n, m, target + 1)
  }
}

spec fn valid_input(n: int, m: int, k: int) -> bool {
  1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8) -> (result: i8)
  requires valid_input(n as int, m as int, k as int)
  ensures 
    1 <= result as int <= (n as int) * (m as int),
    count_less_or_equal_value(n as int, m as int, result as int) >= k as int,
    result as int == 1 || count_less_or_equal_value(n as int, m as int, (result as int) - 1) < k as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix overflow issues and invariant violations */
    // Since n, m can be up to 500000, we need i64 for computations
    // but inputs are i8, so we work within i8 bounds
    assert(n as int <= 127 && m as int <= 127); // i8 max is 127
    assert((n as int) * (m as int) <= 127 * 127);
    
    let mut low: i64 = 1;
    let mut high: i64 = if (n as i64) * (m as i64) <= 127 { (n as i64) * (m as i64) } else { 127 };
    let mut result: i64 = 1; // Start with valid value
    
    // Initial computation to ensure result invariant
    let mut count: i64 = 0;
    let mut i: i64 = 1;
    while i <= n as i64
        invariant
            1 <= i <= (n as i64) + 1,
            0 <= count <= (n as i64) * (m as i64)
        decreases (n as i64) - i + 1
    {
        count = count + (m as i64);
        i = i + 1;
    }
    
    if count >= k as i64 {
        result = high;
    }
    
    while low <= high
        invariant
            1 <= low as int <= (n as int) * (m as int) + 1,
            0 <= high as int <= (n as int) * (m as int),
            1 <= result as int <= (n as int) * (m as int),
            count_less_or_equal_value(n as int, m as int, result as int) >= k as int,
            low as int <= high as int + 1,
            forall|x: int| low as int <= x <= (n as int) * (m as int) ==> count_less_or_equal_value(n as int, m as int, x) >= k as int ==> result as int <= x,
            forall|x: int| 1 <= x < low as int ==> count_less_or_equal_value(n as int, m as int, x) < k as int
        decreases high - low + 1
    {
        let mid: i64 = low + (high - low) / 2;
        assert(1 <= mid <= (n as i64) * (m as i64));
        
        let mut count: i64 = 0;
        let mut i: i64 = 1;
        
        while i <= n as i64
            invariant
                1 <= i <= (n as i64) + 1,
                0 <= count <= (n as i64) * (m as i64)
            decreases (n as i64) - i + 1
        {
            let row_count = if mid / i < m as i64 { mid / i } else { m as i64 };
            assert(0 <= row_count <= m as i64);
            count = count + row_count;
            assert(count <= i * (m as i64));
            i = i + 1;
        }
        
        proof {
            assert(count as int == count_less_value(n as int, m as int, mid as int + 1));
            assert(count as int == count_less_or_equal_value(n as int, m as int, mid as int));
        }
        
        if count >= k as i64 {
            result = mid;
            high = mid - 1;
        } else {
            low = mid + 1;
        }
    }
    
    assert(1 <= result <= 127);
    #[verifier::truncate]
    (result as i8)
}
// </vc-code>


}

fn main() {}