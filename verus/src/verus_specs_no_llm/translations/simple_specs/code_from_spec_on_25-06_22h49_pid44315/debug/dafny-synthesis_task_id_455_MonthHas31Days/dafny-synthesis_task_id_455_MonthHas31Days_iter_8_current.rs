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
    month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12
}

}

The code you provided is actually correct. The function `MonthHas31Days`:


The ensures clause matches exactly what the function body computes, so the verification should succeed. If you're still getting verification errors, it might be due to:


The code as written should verify correctly in Verus, as the postcondition directly matches the return expression.