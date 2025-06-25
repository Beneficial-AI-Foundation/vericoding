// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn counting_bits(n: int) -> (result: Vec<int>)
    requires 0 <= n <= 100000
    ensures result.len() == n + 1,
            forall|i: int| 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2
{
}

}