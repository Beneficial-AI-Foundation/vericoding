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
/* helper modified by LLM (iteration 5): changed parameter and return to u64 to fix compilation error with int in exec code */fn count_digits_7(x: u64) -> (result: u64)
    ensures
        result as nat == count7_r(x as nat),
    decreases x
{
    if x < 10u64 {
        if x == 7u64 { 1u64 } else { 0u64 }
    } else {
        let lst: u64 = if x % 10u64 == 7u64 { 1u64 } else { 0u64 };
        lst + count_digits_7(x / 10u64)
    }
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
    /* code modified by LLM (iteration 5): changed acc and i to u64, adjusted cast to u64 in helper call */
    let mut acc: u64 = 0u64;
    let mut i: u64 = 0u64;
    while i < n as u64
        invariant
            acc as nat == sum(
                Seq::new(i as nat, |j: int| 
                    if 0 <= j < i as nat && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0 }
                )
            ),
            0 <= i <= n as u64,
        decreases n as u64 - i
    {
        if (i as u32 % 11) == 0 || (i as u32 % 13) == 0 {
            let cnt = count_digits_7(i as u64);
            acc += cnt as u64;
        }
        i += 1u64;
    }
    proof {
        assert(acc as nat == sum(
            Seq::new(n as nat, |j: int| 
                if 0 <= j < n as nat && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0 }
            )
        ));
    }
    acc as u8
}
// </vc-code>


}

fn main() {}