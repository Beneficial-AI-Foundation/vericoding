use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MonthHas31Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12,
    ensures
        result <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12),
{
    let has_31_days = month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12;
    
    // The postcondition should be automatically satisfied since we're returning
    // exactly what the ensures clause specifies
    has_31_days
}

}