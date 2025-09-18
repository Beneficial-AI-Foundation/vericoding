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
/* helper modified by LLM (iteration 5): spec constructor for TimeDelta64 */
spec fn mk_timedelta64_spec(value: i64, unit: TimeUnit) -> TimeDelta64 { TimeDelta64 { value: value, unit: unit } }
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
{
    /* code modified by LLM (iteration 5): construct and return TimeDelta64 */
    let result = TimeDelta64 { value: value, unit: unit };
    result
}
// </vc-code>

}
fn main() {}