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
fn unit_to_string(unit: TimeUnit) -> String {
        match unit {
            TimeUnit::Years => "Years".to_string(),
            TimeUnit::Days => "Days".to_string(),
            TimeUnit::Hours => "Hours".to_string(),
            TimeUnit::Minutes => "Minutes".to_string(),
            TimeUnit::Seconds => "Seconds".to_string(),
            TimeUnit::Milliseconds => "Milliseconds".to_string(),
            TimeUnit::Microseconds => "Microseconds".to_string(),
            TimeUnit::Nanoseconds => "Nanoseconds".to_string(),
        }
    }

/* helper modified by LLM (iteration 5): replaced string concatenation with String::push_str to avoid internal error */
fn convert_datetime_to_string(dt: DateTime64, timezone: TimezoneOption) -> String {
    let unit_str = unit_to_string(dt.unit);
    let tz_str = match timezone {
        TimezoneOption::Naive => {
            if dt.is_utc {
                "UTC".to_string()
            } else {
                "Local".to_string()
            }
        },
        TimezoneOption::UTC => "UTC".to_string(),
        TimezoneOption::Local => "Local".to_string(),
    };
    let offset_str = dt.offset.to_string();
    let mut result = String::new();
    result.push_str(&offset_str);
    result.push(' ');
    result.push_str(&unit_str);
    result.push(' ');
    result.push_str(&tz_str);
    result
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
    /* code modified by LLM (iteration 5): no changes needed */
    let mut result = Vec::new();
    for i in 0..arr.len() {
        let dt = arr[i];
        let s = convert_datetime_to_string(dt, timezone);
        result.push(s);
    }
    result
}
// </vc-code>

}
fn main() {}