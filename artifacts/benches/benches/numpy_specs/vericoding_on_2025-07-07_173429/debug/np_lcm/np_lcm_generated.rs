use vstd::prelude::*;

verus! {

spec fn gcd(a: nat, b: nat) -> nat
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, (b - a) as nat)
    } else {
        gcd((a - b) as nat, b)
    }
}

spec fn lcm_int(a: nat, b: nat) -> nat {
    if a == 0 || b == 0 {
        0
    } else {
        (a * b) / gcd(a, b)
    }
}

proof fn lemma_gcd_positive(a: nat, b: nat)
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
    decreases a + b
{
    if a == 0 {
        assert(gcd(a, b) == b);
    } else if b == 0 {
        assert(gcd(a, b) == a);
    } else if a <= b {
        lemma_gcd_positive(a, (b - a) as nat);
    } else {
        lemma_gcd_positive((a - b) as nat, b);
    }
}

fn gcd_exec(a: u32, b: u32) -> (result: u32)
    ensures result == gcd(a as nat, b as nat)
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd_exec(a, b - a)
    } else {
        gcd_exec(a - b, b)
    }
}

fn lcm_int_exec(a: u32, b: u32) -> (result: u32) {
    if a == 0 || b == 0 {
        0
    } else {
        proof {
            lemma_gcd_positive(a as nat, b as nat);
        }
        let gcd_val = gcd_exec(a, b);
        assert(gcd_val > 0);
        
        let a_64 = a as u64;
        let b_64 = b as u64; 
        
        // Use saturating arithmetic to avoid overflow
        let product = a_64.checked_mul(b_64);
        match product {
            Some(prod) => {
                let result_64 = prod / (gcd_val as u64);
                if result_64 <= u32::MAX as u64 {
                    result_64 as u32
                } else {
                    u32::MAX  // saturate on overflow
                }
            }
            None => u32::MAX  // saturate on overflow
        }
    }
}

fn lcm(a: &[u32], b: &[u32]) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
{
    let mut res = Vec::new();
    let mut i = 0usize;
    let len = a.len();
    
    while i < len
        invariant 
            0 <= i <= len,
            res.len() == i,
            len == a.len(),
            len == b.len(),
        decreases len - i,
    {
        let lcm_val = lcm_int_exec(a[i], b[i]);
        res.push(lcm_val);
        i += 1;
    }
    res
}

}

fn main() {}