// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isMax(m: int, numbers: Seq<int>) -> bool
{
    false
}

spec fn spec_max(numbers: Seq<int>) -> result: int
    requires
        numbers != []
    ensures
        isMax(result, numbers)
;

proof fn lemma_max(numbers: Seq<int>) -> (result: int)
    requires
        numbers != []
    ensures
        isMax(result, numbers)
{
    0
}

}