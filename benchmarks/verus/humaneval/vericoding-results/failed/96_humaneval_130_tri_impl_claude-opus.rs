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

// </vc-helpers>

// <vc-spec>
fn tribonacci(n: u8) -> (result: Vec<u8>)
  ensures 
    result.len() == n as int + 1 &&
    (forall|i: int| 0 <= i <= n as int ==> result[i] as nat == tri(i as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and assertions for arithmetic operations */
    let mut result = Vec::new();
    let mut i: u8 = 0;
    
    while i <= n
        invariant
            i <= n + 1,
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] as nat == tri(j as nat),
        decreases (n as int + 1) - i as int
    {
        if i == 0 {
            result.push(1);
        } else if i == 1 {
            result.push(3);
        } else if i % 2 == 0 {
            let val = 1 + i / 2;
            result.push(val);
        } else {
            // For odd i > 1: tri(i) = tri(i-1) + tri(i-2) + tri(i+1)
            let val1 = result[(i - 1) as usize];
            let val2 = result[(i - 2) as usize];
            // tri(i+1) where i+1 is even: tri(i+1) = 1 + (i+1)/2
            assert(i < 255); // ensure i+1 doesn't overflow
            let i_plus_1 = (i + 1) as int;
            assert(i_plus_1 / 2 < 255);
            let val3: u8 = (1 + i_plus_1 / 2) as u8;
            assert((val1 as int + val2 as int) < 256);
            assert((val1 as int + val2 as int + val3 as int) < 256);
            let sum = ((val1 as int + val2 as int + val3 as int) as u8);
            result.push(sum);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}