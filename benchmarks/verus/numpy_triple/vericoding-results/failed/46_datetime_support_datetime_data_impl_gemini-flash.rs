// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Datetime unit enumeration representing the time scales used in datetime operations */
#[derive(PartialEq, Eq, Structural)]
pub enum DatetimeUnit {
    /* Years */
    Y,
    /* Months */
    M,
    /* Weeks */
    W,
    /* Days */
    D,
    /* Hours */
    H,
    /* Minutes */
    Min,
    /* Seconds */
    S,
    /* Milliseconds */
    Ms,
    /* Microseconds */
    Us,
    /* Nanoseconds */
    Ns,
}

/* Structure containing datetime type information including unit and count */
#[derive(PartialEq, Eq, Structural)]
pub struct DatetimeTypeInfo {
    /* The time unit (seconds, minutes, hours, etc.) */
    pub unit: DatetimeUnit,
    /* The count of base units in a step (e.g., 25 for "25 seconds") */
    pub count: nat,
}

/* Datetime dtype representing either datetime64 or timedelta64 types */
#[derive(PartialEq, Eq, Structural)]
pub enum DatetimeDtype {
    /* A datetime64 type with specified unit and count */
    Datetime64(DatetimeTypeInfo),
    /* A timedelta64 type with specified unit and count */
    Timedelta64(DatetimeTypeInfo),
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `u8::max_value()` is used for comparison, ensuring the 'nat' value is correctly checked against the maximum `u8` value and then cast to `u8`. */
fn to_u8_sat(n: nat) -> u8 {
    if (n@) >= u8::max_value() as nat {
        u8::max_value()
    } else {
        n@ as u8
    }
}
// </vc-helpers>

// <vc-spec>
fn datetime_data(dtype: DatetimeDtype) -> (result: (DatetimeUnit, u8))
    ensures
        match dtype {
            DatetimeDtype::Datetime64(info) => result == (info.unit, info.count as u8) && info.count > 0,
            DatetimeDtype::Timedelta64(info) => result == (info.unit, info.count as u8) && info.count > 0,
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated the `Datetime64` and `Timedelta64` arms of the `match` statement to use the `to_u8_sat` helper function, removing reliance on direct `as u8` casts for `info.count` to ensure proper handling of `nat` to `u8` conversion. */
{
    match dtype {
        DatetimeDtype::Datetime64(info) => {
            (info.unit, to_u8_sat(info.count))
        },
        DatetimeDtype::Timedelta64(info) => {
            (info.unit, to_u8_sat(info.count))
        },
    }
}
// </vc-code>


}
fn main() {}