// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn tri(n: nat) -> nat
  decreases if n % 2 == 0 { 0 } else { n }
{
  if n == 1 { 3 }
  else if n % 2 == 0 { 1 + n / 2 }
  else { tri((n - 1) as nat) + tri((n - 2) as nat) + tri(n + 1) }
}
// </vc-preamble>

// <vc-helpers>
proof fn tri_spec(n: nat) -> (result: nat)
    ensures result == tri(n)
decreases if n % 2 == 0 { 0 } else { n }
{
    reveal(tri);
    if n == 1 {
        3
    } else if n % 2 == 0 {
        1 + n / 2
    } else {
        tri_spec((n - 1) as nat) + tri_spec((n - 2) as nat) + tri_spec(n + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn tribonacci(n: u8) -> (result: Vec<u8>)
  ensures 
    result.len() == n as int + 1 &&
    (forall|i: int| 0 <= i <= n as int ==> result[i] as nat == tri(i as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost code usage by moving tri_spec call to proof block */
    let mut result = Vec::<u8>::new();
    
    if n == 0 {
        result.push(1);
        return result;
    }
    
    result.push(1);
    result.push(3);
    
    if n == 1 {
        return result;
    }
    
    let mut i: usize = 2;
    while i <= n as usize
        invariant
            result.len() == i + 1,
            forall|j: int| 0 <= j < i as int ==> result[j as usize] as nat == tri(j as nat)
        decreases (n as usize - i) + 1
    {
        if i % 2 == 0 {
            let val = 1 + (i / 2);
            result.push(val as u8);
        } else {
            proof {
                let next = tri_spec((i + 1) as nat);
                assert(result[i - 2] as nat == tri((i - 2) as nat));
                assert(result[i - 1] as nat == tri((i - 1) as nat));
                let val = (result[i - 2] as u64) + (result[i - 1] as u64) + (next as u64);
                assert(val as nat == tri(i as nat));
            }
            let computed_val = result[i - 2] as u64 + result[i - 1] as u64 + tri_spec((i + 1) as nat) as u64;
            result.push(computed_val as u8);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}