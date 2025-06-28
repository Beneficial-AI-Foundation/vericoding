use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcProduct(m: nat, n: nat) -> (res: nat)
    ensures
        res == m*n
{
    return m * n;
}

}