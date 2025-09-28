use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
fn f_exec(n: usize) -> (res: usize)
    requires
        true,
    ensures
        res as nat == f(n as nat),
    decreases
        (n as nat),
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        let q = n / 2;
        1 + 2 * f_exec(q)
    } else {
        2 * f_exec(n / 2)
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    let n_usize: usize = n as usize;
    let res_usize: usize = f_exec(n_usize);
    res_usize as u64
}
// </vc-code>

fn main() {}

}