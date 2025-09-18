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
/* helper modified by LLM (iteration 5): replaced undefined new_strlit with String::from for string literals */
exec fn positive_int64_to_string(n: u64) -> (result: String)
    ensures result@.len() > 0
{
    n.to_string()
}

exec fn timeunit_string(unit: TimeUnit) -> (result: String)
    ensures result@.len() > 0
{
    String::from(
        match unit {
            TimeUnit::Years => "Years",
            TimeUnit::Days => "Days",
            TimeUnit::Hours => "Hours",
            TimeUnit::Minutes => "Minutes",
            TimeUnit::Seconds => "Seconds",
            TimeUnit::Milliseconds => "Milliseconds",
            TimeUnit::Microseconds => "Microseconds",
            TimeUnit::Nanoseconds => "Nanoseconds",
        }
    )
}

exec fn datetime_to_string(dt: DateTime64) -> (result: String)
    ensures result@.len() > 0
{
    let offset_str = if dt.offset < 0 {
        let mut s = String::from("-");
        s.push_str(&positive_int64_to_string((-dt.offset) as u64));
        s
    } else {
        positive_int64_to_string(dt.offset as u64)
    };
    let unit_str = timeunit_string(dt.unit);
    let mut full_str = offset_str;
    full_str.push_str(" ");
    full_str.push_str(&unit_str);
    if dt.is_utc {
        full_str.push_str(" UTC");
    } else {
        full_str.push_str(" Local");
    }
    full_str
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
    /* code modified by LLM (iteration 4): fixed compilation errors by changing loop variable from nat to usize, removing casts to nat */
    let mut result = Vec::<String>::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant 0 <= i <= arr.len()
    {
        let dt = arr[i];
        let s = datetime_to_string(dt);
        result.push(s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}