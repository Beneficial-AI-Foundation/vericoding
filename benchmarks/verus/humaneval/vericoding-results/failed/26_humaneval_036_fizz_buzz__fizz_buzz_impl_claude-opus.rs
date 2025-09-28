// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count7_r(x: nat) -> nat
    decreases x
{
    let lst = if x % 10 == 7 { 1 } else { 0 };
    if x < 10 { lst } else { lst + count7_r(x / 10) }
}

spec fn sum(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count7_decomposition(x: nat)
    ensures
        x >= 10 ==> count7_r(x) == (if x % 10 == 7 { 1nat } else { 0nat }) + count7_r(x / 10),
        x < 10 ==> count7_r(x) == if x % 10 == 7 { 1nat } else { 0nat },
    decreases x
{
    // Follows directly from the definition of count7_r
}

/* helper modified by LLM (iteration 5): Fixed type annotations in lemma */
// </vc-helpers>

// <vc-spec>
fn fizz_buzz(n: u8) -> (result: u8)
    ensures result as nat == sum(
        Seq::new(n as nat, |i: int| 
            if 0 <= i < n as nat && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
        )
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementation with correct count7 counting */
    let mut total: u8 = 0;
    let mut i: u8 = 0;
    
    while i < n
        invariant
            i <= n,
            total as nat == sum(
                Seq::new(i as nat, |j: int| 
                    if 0 <= j < i && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0 }
                )
            ),
        decreases n - i
    {
        if i % 11 == 0 || i % 13 == 0 {
            // Count the number of 7s in i
            let mut x: u32 = i as u32;
            let mut count: u8 = 0;
            let orig_x = x;
            
            // We'll count 7s directly by examining each digit
            while x > 0
                invariant
                    orig_x == i as u32,
                    count as nat + count7_r(x as nat) == count7_r(orig_x as nat),
                decreases x
            {
                proof {
                    lemma_count7_decomposition(x as nat);
                }
                if x % 10 == 7 {
                    count = count + 1;
                }
                x = x / 10;
            }
            
            // Now count == count7_r(i as nat) since count7_r(0) == 0
            total = total + count;
        }
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}