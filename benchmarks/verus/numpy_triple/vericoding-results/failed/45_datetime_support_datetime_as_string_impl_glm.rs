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
use std::string::String;

/* helper modified by LLM (iteration 5): replaced String::new() with String::from("DT") to avoid compilation error */
fn datetime64_to_string(dt: DateTime64, timezone: TimezoneOption) -> (s: String)
    ensures s@.len() > 0
{
    let unit_str = match dt.unit {
        TimeUnit::Years => "Y",
        TimeUnit::Days => "D",
        TimeUnit::Hours => "h",
        TimeUnit::Minutes => "m",
        TimeUnit::Seconds => "s",
        TimeUnit::Milliseconds => "ms",
        TimeUnit::Microseconds => "μs",
        TimeUnit::Nanoseconds => "ns",
    };

    let timezone_str = match timezone {
        TimezoneOption::Naive => "",
        TimezoneOption::UTC => if dt.is_utc { "UTC" } else { "non-UTC" },
        TimezoneOption::Local => if dt.is_utc { "UTC" } else { "Local" },
    };

    let mut s = String::from("DT");
    s.push_str(&dt.offset.to_string());
    s.push_str(unit_str);
    if timezone != TimezoneOption::Naive {
        s.push_str(timezone_str);
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn datetime_as_string(arr: Vec<DateTime64>, timezone: TimezoneOption) -> (result: Vec<String>)
    requires arr@.len() > 0,
    ensures 
        result@.len() == arr@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i]@.len() > 0,
// </vc-spec>
// <vc-code>
{
        /* code modified by LLM (iteration 5): no changes to main logic, helper was fixed */
        let mut result: Vec<String> = Vec::new();
        let mut i = 0;
        while i < arr.len()
            invariant 
                0 <= i <= arr@.len(),
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j]@.len() > 0,
            decreases arr@.len() - i
        {
            let dt = arr[i];
            let s = datetime64_to_string(dt, timezone);
            result.push(s);
            i += 1;
        }
        result
    }
// </vc-code>

}
fn main() {}