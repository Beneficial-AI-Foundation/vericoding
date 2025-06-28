use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mystery1(n: nat, m: nat) -> (res: nat)
    ensures n + m == res
{
    n + m
}

fn mystery2(n: nat, m: nat) -> (res: nat)
    requires n + m == n * m
    ensures
        n + m == res,
        n * m == res
{
    n + m
}

}