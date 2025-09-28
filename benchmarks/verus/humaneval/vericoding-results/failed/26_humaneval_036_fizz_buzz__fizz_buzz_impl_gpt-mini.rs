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
/* helper modified by LLM (iteration 5): added fizz_sum */
spec fn fizz_sum(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        let m = n - 1;
        fizz_sum(m) + (if m % 11 == 0 || m % 13 == 0 { count7_r(m) } else { 0 })
    }
}

/* helper modified by LLM (iteration 5): proof that Seq sum equals fizz_sum */
proof fn sum_eq_fizz_sum(n: nat) -> ()
    ensures
        sum(
            Seq::new(n, |i: int|
                if 0 <= i < n && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
            )
        ) == fizz_sum(n),
    decreases n
{
    if n == 0 {
        // base case: both sides are 0
    } else {
        sum_eq_fizz_sum(n - 1);
        proof {
            assert(
                fizz_sum(n) == fizz_sum(n - 1) + (if (n - 1) % 11 == 0 || (n - 1) % 13 == 0 { count7_r(n - 1) } else { 0 })
            );
            assert(
                sum(
                    Seq::new(n, |i: int|
                        if 0 <= i < n && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
                    )
                )
                ==
                sum(
                    Seq::new(n - 1, |i: int|
                        if 0 <= i < n - 1 && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
                    )
                ) + (if (n - 1) % 11 == 0 || (n - 1) % 13 == 0 { count7_r(n - 1) } else { 0 })
            );
            assert(
                sum(
                    Seq::new(n - 1, |i: int|
                        if 0 <= i < n - 1 && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
                    )
                ) == fizz_sum(n - 1)
            );
        }
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
    /* code modified by LLM (iteration 5): removed invalid 'tracked' keyword and use nat locals */
    let mut i: nat = 0;
    let mut acc: nat = 0;
    while i < (n as nat)
        invariant
            acc == fizz_sum(i),
            i <= (n as nat),
        decreases (n as nat) - i
    {
        let add: nat = if i % 11 == 0 || i % 13 == 0 { count7_r(i) } else { 0 };
        acc = acc + add;
        i = i + 1;
    }
    proof {
        assert(acc == fizz_sum(n as nat));
    }
    let result = acc as u8;
    result
}

// </vc-code>


}

fn main() {}