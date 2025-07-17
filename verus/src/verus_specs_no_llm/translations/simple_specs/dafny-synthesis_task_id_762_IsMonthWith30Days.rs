// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsMonthWith30Days(month: int) -> result: bool
    requires
        1 <= month <= 12
    ensures
        result <==> month == 4 | month == 6 .len() month == 9 .len()| month == 11
;

proof fn lemma_IsMonthWith30Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12
    ensures
        result <==> month == 4 | month == 6 .len() month == 9 .len()| month == 11
{
    false
}

}