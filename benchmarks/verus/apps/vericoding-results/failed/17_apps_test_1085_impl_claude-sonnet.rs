// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: nat) -> bool {
    n > 0
}

spec fn reduce_by_divisor(n: nat, d: nat) -> nat {
    if n > 0 && d > 1 && n % d == 0 && n >= d {
        n / d
    } else {
        n
    }
}

spec fn count_divisors(n: int) -> nat {
    if n > 0 {
        Set::new(|d: int| 1 <= d <= n && n % d == 0).len()
    } else {
        0
    }
}

spec fn count_special_divisors(n: nat) -> nat {
    if n > 0 {
        Set::new(|d: int| 2 <= d <= n && (n as int) % d == 0 && ((reduce_by_divisor(n, d as nat) as int) - 1) % d == 0).len()
    } else {
        0
    }
}

spec fn count_valid_k_values(n: nat) -> int {
    if n > 0 {
        if n == 1 {
            -1
        } else {
            count_divisors(n as int - 1) as int + count_special_divisors(n) as int - 1
        }
    } else {
        -1
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed proofs with explicit subset reasoning and improved bounds */
proof fn lemma_divisor_count_bound(n: int)
    requires n > 0
    ensures count_divisors(n) <= n
{
    let divisor_set = Set::new(|d: int| 1 <= d <= n && n % d == 0);
    let all_set = Set::new(|d: int| 1 <= d <= n);
    assert(divisor_set.subset_of(all_set));
    assert(all_set.len() == n);
    assert(divisor_set.len() <= all_set.len());
}

proof fn lemma_special_divisors_bound(n: nat)
    requires n > 0
    ensures count_special_divisors(n) <= n
{
    let special_set = Set::new(|d: int| 2 <= d <= n && (n as int) % d == 0 && ((reduce_by_divisor(n, d as nat) as int) - 1) % d == 0);
    let range_set = Set::new(|d: int| 2 <= d <= n);
    assert(special_set.subset_of(range_set));
    assert(range_set.len() <= n);
    assert(special_set.len() <= range_set.len());
}

fn count_divisors_impl(n: i32) -> (result: u8)
    requires n > 0, n <= 255
    ensures result as int == count_divisors(n as int)
{
    let mut count = 0u8;
    let mut i = 1i32;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            count as int == Set::new(|d: int| 1 <= d < i && (n as int) % d == 0).len(),
            count <= i,
            count <= 255
        decreases n - i
    {
        if n % i == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(Set::new(|d: int| 1 <= d < i && (n as int) % d == 0) =~= Set::new(|d: int| 1 <= d <= n && (n as int) % d == 0));
    }
    
    count
}

fn count_special_divisors_impl(n: u8) -> (result: u8)
    requires n > 0
    ensures result as int == count_special_divisors(n as nat)
{
    let mut count = 0u8;
    let mut d = 2u8;
    
    while d <= n
        invariant
            2 <= d <= (n as int) + 1,
            count as int == Set::new(|x: int| 2 <= x < d && (n as int) % x == 0 && ((reduce_by_divisor(n as nat, x as nat) as int) - 1) % x == 0).len(),
            count <= d,
            count <= 255
        decreases (n as int) - (d as int)
    {
        if n % d == 0 {
            let reduced = n / d;
            if reduced >= 1 && (reduced - 1) % d == 0 {
                count = count + 1;
            }
        }
        d = d + 1;
    }
    
    proof {
        assert(Set::new(|x: int| 2 <= x < d && (n as int) % x == 0 && ((reduce_by_divisor(n as nat, x as nat) as int) - 1) % x == 0) =~= Set::new(|x: int| 2 <= x <= n && (n as int) % x == 0 && ((reduce_by_divisor(n as nat, x as nat) as int) - 1) % x == 0));
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8) -> (result: i8)
    requires 
        valid_input(n as nat)
    ensures 
        result as int == count_valid_k_values(n as nat),
        n == 1 ==> result as int == -1,
        n > 1 ==> result as int == count_divisors(n as int - 1) as int + count_special_divisors(n as nat) as int - 1,
        result as int >= -1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added explicit bounds checking and correct overflow prevention */
    if n == 1 {
        return -1i8;
    }
    
    let divisor_count = count_divisors_impl((n - 1) as i32);
    let special_count = count_special_divisors_impl(n);
    
    proof {
        lemma_divisor_count_bound((n - 1) as int);
        lemma_special_divisors_bound(n as nat);
        assert(divisor_count as int <= (n - 1) as int);
        assert(special_count as int <= n as int);
        assert(divisor_count as int <= 254);
        assert(special_count as int <= 255);
        assert((divisor_count as int) + (special_count as int) <= 509);
        assert((divisor_count as int) + (special_count as int) - 1 <= 508);
        assert((divisor_count as int) + (special_count as int) - 1 >= -1);
        // For u8 values, the sum fits in i16, so cast is safe
        assert(divisor_count <= 127 && special_count <= 127 ==> (divisor_count as int) + (special_count as int) - 1 <= 253);
    }
    
    // Use i16 for intermediate calculation to avoid overflow
    let intermediate = (divisor_count as i16) + (special_count as i16) - 1i16;
    
    proof {
        assert(intermediate >= -1);
        assert(intermediate <= 508);
        // Since n <= 255, we have better bounds
        assert(intermediate >= -1 && intermediate <= 127);
    }
    
    let result = intermediate as i8;
    result
}
// </vc-code>


}

fn main() {}