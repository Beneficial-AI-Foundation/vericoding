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
/* helper modified by LLM (iteration 5): remove duplicate enum definition */
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
/* code modified by LLM (iteration 5): Remove unnecessary assertion for other time units */
{
    let result = DateTime64 {
        offset: offset,
        unit: unit,
        is_utc: true,
    };
    match unit {
        TimeUnit::Years => {
            assert(result.offset + 1970 >= 1 && result.offset + 1970 <= 9999);
        }
        TimeUnit::Days | TimeUnit::Hours | TimeUnit::Minutes | TimeUnit::Seconds => {
            assert(result.offset >= -2147483648 && result.offset <= 2147483647);
        }
        _ => {},
    }
    result
}
// </vc-code>

}
fn main() {}