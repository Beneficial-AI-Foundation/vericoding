use vstd::prelude::*;

spec fn pow(base: int, exponent: int) -> int
    recommends exponent >= 0
{
    if exponent == 0 { 1 }
    else if exponent % 2 == 0 { pow(base * base, exponent / 2) }
    else { base * pow(base, exponent - 1) }
}

pub fn do_algebra(operators: Seq<char>, operands: Seq<int>) -> (result: int)
    requires
        operators.len() != 0 && operands.len() != 0 && operators.len() + 1 == operands.len(),
        forall|i: int| 0 <= i < operands.len() ==> operands[i] >= 0,
{
}