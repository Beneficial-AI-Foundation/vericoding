// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn do_algebra(operators: Seq<char>, operands: Seq<int>) -> (result: int)
    requires operators != [] and operands != [] and operators.len() + 1 == operands.len(),
             forall|i: int| 0 <= i < operands.len() ==> operands[i] >= 0
{
}

}