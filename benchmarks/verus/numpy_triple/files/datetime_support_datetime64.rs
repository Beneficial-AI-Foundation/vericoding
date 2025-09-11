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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}