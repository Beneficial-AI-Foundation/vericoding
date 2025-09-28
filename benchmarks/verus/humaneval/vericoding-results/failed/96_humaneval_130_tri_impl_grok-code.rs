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
/* helper modified by LLM (iteration 5): moved correctness proof from separate proof fn to ensures on tri_exec, added requires for bounds, fixed recursive calls */
fn tri_exec(n: u64) -> (result: u64)
    requires 0 <= n <= 255
    ensures result == tri(n as nat)
    decreases if n % 2 == 0 { 0 } else { n as nat }
{
    if n == 1 {
        3
    } else if n % 2 == 0 {
        1 + n / 2
    } else {
        tri_exec(n - 1) + tri_exec(n - 2) + tri_exec(n + 1)
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
    /* code modified by LLM (iteration 5): removed assumption and empty vec, implemented loop to compute tribonacci sequence, removed proof call since ensures now on tri_exec */
    let mut result: Vec<u8> = Vec::new();
    let num: u64 = n as u64;
    let mut i: u64 = 0;
    while i <= num
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as nat == tri(j as nat)
    {
        let val: u8 = tri_exec(i) as u8;
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}