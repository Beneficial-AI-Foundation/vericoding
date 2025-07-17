// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn pow(base: int, exponent: int) -> int
    requires
        exponent >= 0
{
    0
}

spec fn spec_do_algebra(operators: Seq<char>, operands: Seq<int>) -> result: int
    requires
        operators != [] && operands != [] && operators.len() + 1 == operands.len(),
        forall |i: int| 0 <= i < operands.len() ==> operands.index(i) >= 0
;

proof fn lemma_do_algebra(operators: Seq<char>, operands: Seq<int>) -> (result: int)
    requires
        operators != [] && operands != [] && operators.len() + 1 == operands.len(),
        forall |i: int| 0 <= i < operands.len() ==> operands.index(i) >= 0
{
    0
}

}