// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Remove unused helpers and keep only what's needed */
proof fn timedelta64_invariants_hold(value: i64, unit: TimeUnit)
    ensures
        value >= -9223372036854775808i64,
        value <= 9223372036854775807i64,
{
    // All i64 values are within i64 bounds by definition
}
// </vc-helpers>

// <vc-spec>
fn timedelta64(value: i64, unit: TimeUnit) -> (result: TimeDelta64)
    ensures 
        result.value == value,
        result.unit == unit,
        result.value >= -9223372036854775808i64,
        result.value <= 9223372036854775807i64,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Remove reference to undefined 'result' variable and return struct directly */
{
    TimeDelta64 { value, unit }
}
// </vc-code>

}
fn main() {}