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
/* helper modified by LLM (iteration 5): predicate for valid year offsets so that 1970 + offset is in [1, 9999] */
spec fn in_years_range(offset: i64) -> bool { offset >= -1969 && offset <= 8029 }

/* helper modified by LLM (iteration 5): predicate for i32-compatible offsets */
spec fn in_i32_range(offset: i64) -> bool { offset >= -2147483648 && offset <= 2147483647 }

/* helper modified by LLM (iteration 5): arithmetic lemma lifting years-range to calendar bound */
proof fn lemma_years_bounds_implication(offset: i64)
    requires in_years_range(offset)
    ensures (offset as int) + 1970 >= 1 && (offset as int) + 1970 <= 9999
{ }

/* helper modified by LLM (iteration 5): arithmetic lemma lifting i32-range to int inequalities */
proof fn lemma_i32_range_lifts(offset: i64)
    requires in_i32_range(offset)
    ensures (offset as int) >= -2147483648 && (offset as int) <= 2147483647
{ }
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
    /* code modified by LLM (iteration 5): construct result directly and add local proof hints; avoid unreachable calls */
    let result_val = DateTime64 { offset, unit, is_utc: true };
    proof {
        assert(result_val.offset == offset);
        assert(result_val.unit == unit);
        assert(result_val.is_utc == true);
        match unit {
            TimeUnit::Years => {
                if offset >= -1969 && offset <= 8029 {
                    assert(in_years_range(offset));
                    lemma_years_bounds_implication(offset);
                }
            }
            TimeUnit::Days | TimeUnit::Hours | TimeUnit::Minutes | TimeUnit::Seconds => {
                if offset >= -2147483648 && offset <= 2147483647 {
                    assert(in_i32_range(offset));
                    lemma_i32_range_lifts(offset);
                }
            }
            TimeUnit::Milliseconds | TimeUnit::Microseconds | TimeUnit::Nanoseconds => { }
        }
    }
    result_val
}
// </vc-code>

}
fn main() {}