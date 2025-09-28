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
spec fn is_divisible_by_11_or_13(i: int) -> bool {
    i % 11 == 0 || i % 13 == 0
}

spec fn get_count7(i: int) -> nat {
    if is_divisible_by_11_or_13(i) { count7_r(i as nat) } else { 0 }
}

fn compute_sum(n: u8) -> (result: u8)
    ensures result as nat == sum(Seq::new(n as nat, |i: int| get_count7(i)))
{
    let mut i: u8 = 0;
    let mut total: u8 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            total as nat == sum(Seq::new(i as nat, |j: int| get_count7(j))),
        decreases n - i,
    {
        if i % 11 == 0 || i % 13 == 0 {
            let count = count7_r(i as nat);
            assert(total as nat + count < (u8::MAX as nat)) by (compute_only);
            total = total + count as u8;
        }
        i = i + 1;
    }
    
    total
}
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
    compute_sum(n)
}
// </vc-code>


}

fn main() {}