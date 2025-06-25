use vstd::prelude::*;

verus! {

spec fn pow(base: int, exponent: int) -> int
    recommends exponent >= 0
{
    if exponent == 0 { 1 }
    else if exponent % 2 == 0 { pow(base * base, exponent / 2) }
    else { base * pow(base, exponent - 1) }
}

pub fn do_algebra(operators: Seq<char>, operands: Seq<int>) -> (result: int)
    requires
        operators != Seq::<char>::empty() && operands != Seq::<int>::empty() && operators.len() + 1 == operands.len(),
        forall|i: int| 0 <= i < operands.len() ==> operands[i] >= 0,
{
}

}