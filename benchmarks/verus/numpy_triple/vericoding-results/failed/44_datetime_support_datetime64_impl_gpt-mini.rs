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
/* helper modified by LLM (iteration 5): constructor that returns a DateTime64 with is_utc true */
fn make_datetime64(offset: i64, unit: TimeUnit) -> DateTime64 {
    DateTime64 { offset: offset, unit: unit, is_utc: true }
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
    /* code modified by LLM (iteration 5): construct DateTime64 and discharge simple proof obligations where possible */
    let result = make_datetime64(offset, unit);
    proof {
        match unit {
            TimeUnit::Years => {
                // For the Years case the specification requires that the represented year (offset + 1970)
                // lies in [1, 9999]. We assert the identity properties of the constructed value so the
                // verifier can relate `result` to the inputs. The numeric bound must hold for valid
                // inputs; callers are expected to provide such offsets for Years.
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
                // the following two asserts state the required year-range property
                assert(result.offset + 1970 >= 1);
                assert(result.offset + 1970 <= 9999);
            }
            TimeUnit::Days => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
                assert(result.offset >= (-2147483648i64));
                assert(result.offset <= 2147483647i64);
            }
            TimeUnit::Hours => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
                assert(result.offset >= (-2147483648i64));
                assert(result.offset <= 2147483647i64);
            }
            TimeUnit::Minutes => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
                assert(result.offset >= (-2147483648i64));
                assert(result.offset <= 2147483647i64);
            }
            TimeUnit::Seconds => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
                assert(result.offset >= (-2147483648i64));
                assert(result.offset <= 2147483647i64);
            }
            TimeUnit::Milliseconds => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
            }
            TimeUnit::Microseconds => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
            }
            TimeUnit::Nanoseconds => {
                assert(result.offset == offset);
                assert(result.unit == unit);
                assert(result.is_utc == true);
            }
        }
    }
    result
}

// </vc-code>

}
fn main() {}