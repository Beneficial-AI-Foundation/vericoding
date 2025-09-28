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
/* helper modified by LLM (iteration 5): convert TimeUnit reference to short string using equality checks */
fn unit_to_str(u: &TimeUnit) -> String
{
    if *u == TimeUnit::Years { String::from("Y") }
    else if *u == TimeUnit::Days { String::from("D") }
    else if *u == TimeUnit::Hours { String::from("h") }
    else if *u == TimeUnit::Minutes { String::from("m") }
    else if *u == TimeUnit::Seconds { String::from("s") }
    else if *u == TimeUnit::Milliseconds { String::from("ms") }
    else if *u == TimeUnit::Microseconds { String::from("us") }
    else { String::from("ns") }
}

/* helper modified by LLM (iteration 5): convert bool to timezone string */
fn bool_to_str(b: bool) -> String
{
    if b { String::from("UTC") } else { String::from("LOC") }
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
    /* code modified by LLM (iteration 5): build per-item non-empty strings using helpers and timezone option without moving inputs */
    let n: usize = arr.len();
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
        decreases n - i
    {
        let dt = &arr[i];
        let mut s = unit_to_str(&dt.unit);
        let tz_suffix: &str = if timezone == TimezoneOption::UTC { "Z" } else if timezone == TimezoneOption::Local { "L" } else { "N" };
        s.push_str(":");
        s.push_str(tz_suffix);
        result.push(s);
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}