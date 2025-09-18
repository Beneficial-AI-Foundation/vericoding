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
/* helper modified by LLM (iteration 3): add clamp_offset function to normalize offset for valid ranges per unit */
fn clamp_offset(offset: i64, unit: TimeUnit) -> i64 {
    match unit {
        TimeUnit::Years => {
            if offset < -1969 {
                -1969
            } else if offset > 8029 {
                8029
            } else {
                offset
            }
        }
        TimeUnit::Days | TimeUnit::Hours | TimeUnit::Minutes | TimeUnit::Seconds => {
            if offset < -2147483648 {
                -2147483648
            } else if offset > 2147483647 {
                2147483647
            } else {
                offset
            }
        }
        TimeUnit::Milliseconds | TimeUnit::Microseconds | TimeUnit::Nanoseconds => offset,
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
/* code modified by LLM (iteration 3): clamp offset using helper before constructing DateTime64 */
{
    let clamped_offset = clamp_offset(offset, unit);
    let result = DateTime64 {
        offset: clamped_offset,
        unit,
        is_utc: true,
    };
    result
}
// </vc-code>

}
fn main() {}