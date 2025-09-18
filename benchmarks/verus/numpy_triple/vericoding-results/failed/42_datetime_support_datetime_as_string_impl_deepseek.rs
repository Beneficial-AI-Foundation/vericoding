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
/* helper modified by LLM (iteration 5): Fixed timezone_string return type and added proper string handling */
proof fn unit_to_seconds(u: TimeUnit) -> (multiplier: int)
    ensures multiplier > 0
{
    match u {
        TimeUnit::Years => 31536000000000000,
        TimeUnit::Days => 86400000000000,
        TimeUnit::Hours => 3600000000000,
        TimeUnit::Minutes => 60000000000,
        TimeUnit::Seconds => 1000000000,
        TimeUnit::Milliseconds => 1000000,
        TimeUnit::Microseconds => 1000,
        TimeUnit::Nanoseconds => 1,
    }
}

fn timezone_string(tz: TimezoneOption) -> (s: String)
    ensures s@.len() > 0
{
    match tz {
        TimezoneOption::Naive => String::from_str(""),
        TimezoneOption::UTC => String::from_str("Z"),
        TimezoneOption::Local => String::from_str("+00:00"),
    }
}

spec fn is_valid_datetime(dt: DateTime64) -> bool {
    dt.offset >= 0 && unit_to_seconds(dt.unit) > 0
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
/* code modified by LLM (iteration 5): Removed format! macro and used manual string construction */
{
    let mut result_vec: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[j]@.len() > 0,
    {
        let dt = arr[i];
        
        let tz_str = timezone_string(timezone);
        let datetime_str = if dt.is_utc {
            let mut s = String::new();
            s.push_str(&dt.offset.to_string());
            s.push_str("Z");
            s
        } else {
            let mut s = String::new();
            s.push_str(&dt.offset.to_string());
            s.push_str(&tz_str);
            s
        };
        
        result_vec.push(datetime_str);
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}