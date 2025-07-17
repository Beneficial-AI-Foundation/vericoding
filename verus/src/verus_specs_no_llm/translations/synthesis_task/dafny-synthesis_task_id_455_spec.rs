// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MonthHas31Days(month: int) -> result: bool
    requires
        1 <= month <= 12
    ensures
        result <==> month in
;

proof fn lemma_MonthHas31Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12
    ensures
        result <==> month in
{
    false
}

}