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
/* helper modified by LLM (iteration 5): added exec function to compute count7 */
proof fn sum_empty()
    ensures sum(Seq::<nat>::empty()) == 0
{
}

proof fn sum_one_element(x: nat)
    ensures sum(seq![x]) == x
{
}

proof fn sum_append_one(s: Seq<nat>, x: nat)
    requires s.len() > 0
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 1 {
        sum_one_element(s[0]);
    } else {
        sum_append_one(s.subrange(1, s.len() as int), x);
    }
}

proof fn sum_prefix_property(s: Seq<nat>, k: nat)
    requires k <= s.len()
    ensures sum(s.subrange(0, k as int)) + sum(s.subrange(k as int, s.len() as int)) == sum(s)
    decreases k
{
    if k == 0 {
    } else if k == s.len() {
    } else {
        sum_prefix_property(s.subrange(1, s.len() as int), (k - 1) as nat);
    }
}

fn count7_exec(x: u8) -> (result: u8)
    ensures result as nat == count7_r(x as nat)
    decreases x
{
    let lst = if x % 10 == 7 { 1 } else { 0 };
    if x < 10 {
        lst
    } else {
        lst + count7_exec(x / 10)
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result: u8 = 0;
    let mut i: u8 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result as nat == sum(
                Seq::new(i as nat, |j: int|
                    if 0 <= j < i as nat && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0 }
                )
            )
        decreases n - i
    {
        if i % 11 == 0 || i % 13 == 0 {
            let count = count7_exec(i);
            result = result + count;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}