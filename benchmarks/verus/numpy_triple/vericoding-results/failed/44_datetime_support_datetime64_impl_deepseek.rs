// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum TimeUnit {

    Years,

    Days,

    Hours,

    Minutes,

    Seconds,

    Milliseconds,

    Microseconds,

    Nanoseconds,
}

pub struct DateTime64 {

    pub offset: i64,

    pub unit: TimeUnit,

    pub is_utc: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return type to bool */
pub proof fn unit_range_constraint(offset: i64, unit: TimeUnit) -> bool
    ensures
        result == match unit {
            TimeUnit::Years => offset + 1970 >= 1 && offset + 1970 <= 9999,
            TimeUnit::Days => offset >= -2147483648 && offset <= 2147483647,
            TimeUnit::Hours => offset >= -2147483648 && offset <= 2147483647,
            TimeUnit::Minutes => offset >= -2147483648 && offset <= 2147483647,
            TimeUnit::Seconds => offset >= -2147483648 && offset <= 2147483647,
            TimeUnit::Milliseconds => true,
            TimeUnit::Microseconds => true,
            TimeUnit::Nanoseconds => true,
        }
{
    match unit {
        TimeUnit::Years => offset + 1970 >= 1 && offset + 1970 <= 9999,
        TimeUnit::Days => offset >= -2147483648 && offset <= 2147483647,
        TimeUnit::Hours => offset >= -2147483648 && offset <= 2147483647,
        TimeUnit::Minutes => offset >= -2147483648 && offset <= 2147483647,
        TimeUnit::Seconds => offset >= -2147483648 && offset <= 2147483647,
        TimeUnit::Milliseconds => true,
        TimeUnit::Microseconds => true,
        TimeUnit::Nanoseconds => true,
    }
}
// </vc-helpers>

// <vc-spec>
fn datetime64(offset: i64, unit: TimeUnit) -> (result: DateTime64)
    ensures 
        result.offset == offset,
        result.unit == unit,
        result.is_utc == true,

        match unit {
            TimeUnit::Years => result.offset + 1970 >= 1 && result.offset + 1970 <= 9999,
            TimeUnit::Days => result.offset >= -2147483648 && result.offset <= 2147483647,
            TimeUnit::Hours => result.offset >= -2147483648 && result.offset <= 2147483647,
            TimeUnit::Minutes => result.offset >= -2147483648 && result.offset <= 2147483647,
            TimeUnit::Seconds => result.offset >= -2147483648 && result.offset <= 2147483647,
            TimeUnit::Milliseconds => true,
            TimeUnit::Microseconds => true,
            TimeUnit::Nanoseconds => true,
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using direct return */
{
    proof {
        assert(unit_range_constraint(offset, unit));
    }
    DateTime64 {
        offset: offset,
        unit: unit,
        is_utc: true,
    }
}
// </vc-code>

}
fn main() {}