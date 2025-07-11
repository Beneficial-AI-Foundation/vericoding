// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BitwiseXOR(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall i :: 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) ^ b.spec_index(i)
{
    return Seq::empty();
}

}