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
/* helper modified by LLM (iteration 5): Remove unnecessary predicate since i64 bounds are inherent */
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
/* code modified by LLM (iteration 5): Remove proof block and simply return TimeDelta64 */
{
    let result = TimeDelta64 { value, unit };
    result
}
// </vc-code>

}
fn main() {}