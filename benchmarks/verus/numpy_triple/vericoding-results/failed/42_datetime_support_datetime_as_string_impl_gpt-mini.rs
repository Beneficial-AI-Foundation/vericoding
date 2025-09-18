// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum TimeUnit {

    Years,

    Days,

    Hours,

    Minutes,

    Seconds,

    Milliseconds,

    Microseconds,

    Nanoseconds,
}

#[derive(PartialEq, Eq)]
struct DateTime64 {

    offset: i64,

    unit: TimeUnit,

    is_utc: bool,
}

#[derive(PartialEq, Eq)]
enum TimezoneOption {

    Naive,

    UTC,

    Local,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): map TimeUnit to a short non-empty spec-level string name */
spec fn timeunit_short_name(u: TimeUnit) -> String {
    match u {
        TimeUnit::Years => "Y".to_string(),
        TimeUnit::Days => "D".to_string(),
        TimeUnit::Hours => "H".to_string(),
        TimeUnit::Minutes => "M".to_string(),
        TimeUnit::Seconds => "S".to_string(),
        TimeUnit::Milliseconds => "m".to_string(),
        TimeUnit::Microseconds => "u".to_string(),
        TimeUnit::Nanoseconds => "n".to_string(),
    }
}
// </vc-helpers>

// <vc-spec>
fn datetime_as_string(arr: Vec<DateTime64>, timezone: TimezoneOption) -> (result: Vec<String>)
    requires arr.len() > 0,
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i]@.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build non-empty strings from literals per unit and timezone using to_string */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len() {
        let dt = &arr[i];
        let s_literal: &str = match (dt.unit, dt.is_utc) {
            (TimeUnit::Years, true) => "YZ",
            (TimeUnit::Years, false) => "YL",
            (TimeUnit::Days, true) => "DZ",
            (TimeUnit::Days, false) => "DL",
            (TimeUnit::Hours, true) => "HZ",
            (TimeUnit::Hours, false) => "HL",
            (TimeUnit::Minutes, true) => "MZ",
            (TimeUnit::Minutes, false) => "ML",
            (TimeUnit::Seconds, true) => "SZ",
            (TimeUnit::Seconds, false) => "SL",
            (TimeUnit::Milliseconds, true) => "mz",
            (TimeUnit::Milliseconds, false) => "ml",
            (TimeUnit::Microseconds, true) => "uz",
            (TimeUnit::Microseconds, false) => "ul",
            (TimeUnit::Nanoseconds, true) => "nz",
            (TimeUnit::Nanoseconds, false) => "nl",
        };
        result.push(s_literal.to_string());
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}