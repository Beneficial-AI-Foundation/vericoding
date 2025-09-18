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
/* code modified by LLM (iteration 2): Add proper bounds checking for different time units */
{
    proof {
        match unit {
            TimeUnit::Years => {
                // Year offset must be between 1 and 9999 when added to 1970
                // This means offset must be between 1 - 1970 = -1969 and 9999 - 1970 = 8029
                assert(offset + 1970 >= 1 && offset + 1970 <= 9999);
            }
            TimeUnit::Days | TimeUnit::Hours | TimeUnit::Minutes | TimeUnit::Seconds => {
                // Other time units must be within i32 range
                assert(offset >= -2147483648 && offset <= 2147483647);
            }
            TimeUnit::Milliseconds | TimeUnit::Microseconds | TimeUnit::Nanoseconds => {
                // No restrictions for these units
            }
        }
    }
    DateTime64 { offset, unit, is_utc: true }
}
// </vc-code>

}
fn main() {}