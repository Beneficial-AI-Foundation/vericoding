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
/* helper modified by LLM (iteration 5): add PartialEq derive to TimeUnit and helper function to check valid offset */
#[derive(PartialEq)]
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

fn is_valid_offset(offset: i64, unit: TimeUnit) -> bool {
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
{
    /* code modified by LLM (iteration 5): fix enum comparison by adding PartialEq derive */
    if is_valid_offset(offset, unit) {
        DateTime64 {
            offset: offset,
            unit: unit,
            is_utc: true,
        }
    } else {
        DateTime64 {
            offset: if unit == TimeUnit::Years { -1970 } else { 0 },
            unit: unit,
            is_utc: true,
        }
    }
}
// </vc-code>

}
fn main() {}