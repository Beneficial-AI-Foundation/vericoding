// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn common_divisors(a: int, b: int) -> Set<int>
{
  Set::new(|d: int| 1 <= d <= a && a % d == 0 && b % d == 0)
}

spec fn valid_input(a: int, b: int, k: int) -> bool
{
  a > 0 && b > 0 && k >= 1 && common_divisors(a, b).len() >= k
}

spec fn is_kth_largest_common_divisor(a: int, b: int, k: int, result: int) -> bool
{
  valid_input(a, b, k) ==> (
    result > 0 &&
    a % result == 0 && b % result == 0 &&
    common_divisors(a, b).contains(result) &&
    Set::new(|d: int| common_divisors(a, b).contains(d) && d > result).len() == (k - 1)
  )
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches in invariants by casting usize to int */
    let mut divisors: Vec<i8> = Vec::new();
    let min_val = if a < b { a } else { b };
    let mut i: i8 = 1;
    
    while i <= min_val
        invariant
            1 <= i <= min_val + 1,
            i <= 127,  // Prevent overflow
            forall|j: int| 1 <= j < i && a as int % j == 0 && b as int % j == 0 ==> 
                exists|idx: int| 0 <= idx < divisors@.len() && divisors@[idx] == j as i8,
            forall|idx: int| 0 <= idx < divisors@.len() ==> 
                1 <= divisors@[idx] <= min_val && 
                a as int % divisors@[idx] as int == 0 && 
                b as int % divisors@[idx] as int == 0,
            divisors@.no_duplicates(),
        decreases min_val - i + 1
    {
        if a % i == 0 && b % i == 0 {
            divisors.push(i);
        }
        if i < min_val {
            i = i + 1;
        } else {
            i = min_val + 1;
        }
    }
    
    proof {
        assert(forall|d: int| 1 <= d <= min_val && a as int % d == 0 && b as int % d == 0 ==> 
            exists|idx: int| 0 <= idx < divisors@.len() && divisors@[idx] == d as i8);
    }
    assert(divisors@.len() >= k as int);
    
    if divisors.len() == 0 {
        return 1;  // Should not happen given precondition
    }
    
    let mut j: usize = 0;
    while j < divisors.len()
        invariant
            j <= divisors.len(),
            forall|m: int, n: int| 0 <= m < j && j <= n < divisors@.len() ==> 
                divisors@[m] >= divisors@[n],
            forall|m: int, n: int| 0 <= m < n < j ==> 
                divisors@[m] >= divisors@[n],
        decreases divisors.len() - j
    {
        if j == divisors.len() - 1 {
            j = j + 1;
            continue;
        }
        
        let mut m: usize = j + 1;
        let mut max_idx: usize = j;
        let mut max_val: i8 = divisors[j];
        
        while m < divisors.len()
            invariant
                j < m <= divisors.len(),
                j <= max_idx < m,
                max_val == divisors@[max_idx as int],
                forall|p: int| j <= p < m ==> divisors@[max_idx as int] >= divisors@[p],
            decreases divisors.len() - m
        {
            if divisors[m] > max_val {
                max_idx = m;
                max_val = divisors[m];
            }
            m = m + 1;
        }
        
        if max_idx != j {
            let temp = divisors[j];
            divisors.set(j, divisors[max_idx]);
            divisors.set(max_idx, temp);
        }
        j = j + 1;
    }
    
    proof {
        assert(forall|m: int, n: int| 0 <= m < n < divisors@.len() ==> 
            divisors@[m] >= divisors@[n]);
    }
    
    divisors[(k - 1) as usize]
}
// </vc-code>


}

fn main() {}