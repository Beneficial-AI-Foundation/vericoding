use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsMonthWith30Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12
    ensures
        result <==> (month == 4 || month == 6 || month == 9 || month == 11)
{
    let result = month == 4 || month == 6 || month == 9 || month == 11;
    assert(result <==> (month == 4 || month == 6 || month == 9 || month == 11));
    result
}

}