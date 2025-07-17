// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn Double(val: int) -> (int)
{
    0
}

spec fn spec_TestDouble(val: int) -> val2:int
    ensures
        val2 == Double(val)
;

proof fn lemma_TestDouble(val: int) -> (val2: int)
    ensures
        val2 == Double(val)
{
    0
}

}