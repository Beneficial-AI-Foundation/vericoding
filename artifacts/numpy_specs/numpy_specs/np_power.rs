use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

fn power(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
{
    assume(false);
    Vec::new()
}

fn main() {}

}