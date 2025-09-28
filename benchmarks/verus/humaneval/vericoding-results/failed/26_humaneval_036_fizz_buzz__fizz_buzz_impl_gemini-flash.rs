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
/* helper modified by LLM (iteration 5): removed the `while` loop from `check_count7_r` to make it a pure `spec fn` */
spec fn check_count7_r(num: u8) -> nat {
    count7_r(num as nat)
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
/* code modified by LLM (iteration 5): simplified the inner loop logic, removing `check_count7_r` and directly calculating `count7_r` in the main loop */
{
    let mut i: u8 = 0;
    let mut sum_count7: u8 = 0;

    while i < n
        invariant
            0 <= i && i <= n,
            sum_count7 as nat == sum(Seq::new(i as nat, |j: int|
                if 0 <= j < i as nat && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0 }
            ))
        decreases (n - i) as int
    {
        if i % 11 == 0 || i % 13 == 0 {
            let mut current_count7_val: u8 = 0;
            let mut temp_num_i = i;

            while temp_num_i > 0
                invariant
                    temp_num_i >= 0,
                    current_count7_val as nat + count7_r(temp_num_i as nat) == count7_r(i as nat)
                decreases temp_num_i as int
            {
                if temp_num_i % 10 == 7 {
                    current_count7_val = current_count7_val + 1;
                }
                temp_num_i = temp_num_i / 10;
            }
            sum_count7 = sum_count7 + current_count7_val;
        }
        i = i + 1;
    }
    sum_count7
}
// </vc-code>


}

fn main() {}