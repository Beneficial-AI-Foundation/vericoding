use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum TimeUnit {

    Year,

    Month,

    Week,

    Day,

    Hour,

    Minute,

    Second,

    Millisecond,

    Microsecond,

    Nanosecond,

    Picosecond,

    Femtosecond,

    Attosecond,
}

#[derive(PartialEq, Eq, Structural)]
pub struct TimeDelta64 {

    pub value: i64,

    pub unit: TimeUnit,
}

fn timedelta64(value: i64, unit: TimeUnit) -> (result: TimeDelta64)
    ensures 
        result.value == value,
        result.unit == unit,
        result.value >= -9223372036854775808i64,
        result.value <= 9223372036854775807i64,
{
    assume(false);
    unreached()
}

}
fn main() {}