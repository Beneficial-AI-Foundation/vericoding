use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
exec fn helper_f2(n: u32) -> (a: u32)
    requires n <= 531441
    ensures a as nat == f2(n as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let a = helper_f2(n / 3);
        let b = n % 4;
        let res = 5 * a + b;
        assert(5 * (a as int) + (b as int) <= u32::MAX as int);
        proof {
            assert(f2(n as nat) == 5 * f2((n as nat)/3) + ((n as nat) % 4));
            assert(res as nat == 5 * (a as nat) + (b as nat));
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    helper_f2(n)
}
// </vc-code>

fn main() {}

}