use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcProduct(m: u32, n: u32) -> (res: u32)
    requires
        m <= 0xFFFF,
        n <= 0xFFFF,
    ensures
        res == (m as nat) * (n as nat)
{
    m * n
}

}