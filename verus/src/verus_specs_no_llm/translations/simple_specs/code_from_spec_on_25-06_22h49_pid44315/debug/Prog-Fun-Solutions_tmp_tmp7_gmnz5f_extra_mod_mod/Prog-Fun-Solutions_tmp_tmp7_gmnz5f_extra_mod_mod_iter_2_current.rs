use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn f(n: nat) -> nat {
    n
}

fn mod_fn(n: u32) -> (a: u32)
    requires
        n <= 0xffffffff
    ensures
        a == f(n as nat)
{
    n
}

}