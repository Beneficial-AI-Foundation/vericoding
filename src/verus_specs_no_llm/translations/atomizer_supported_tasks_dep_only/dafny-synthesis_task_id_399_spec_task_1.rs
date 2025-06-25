// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn BitwiseXOR(a: Seq<bv32>, b: Seq<bv32>) -> (result: Seq<bv32>)
    requires a.len() == b.len()
    ensures result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] ^ b[i]
{
}

}