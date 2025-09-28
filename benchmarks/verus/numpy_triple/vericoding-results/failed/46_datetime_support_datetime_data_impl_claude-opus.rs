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
{
    /* code modified by LLM (iteration 5): fix nat to u8 conversion without as_u64() method */
    match dtype {
        DatetimeDtype::Datetime64(info) => {
            assert(info.count > 0);
            assert(info.count <= 255);
            let count_u8: u8 = if info.count <= 255 {
                info.count as u8
            } else {
                255u8
            };
            (info.unit, count_u8)
        },
        DatetimeDtype::Timedelta64(info) => {
            assert(info.count > 0);
            assert(info.count <= 255);
            let count_u8: u8 = if info.count <= 255 {
                info.count as u8
            } else {
                255u8
            };
            (info.unit, count_u8)
        }
    }
}
// </vc-code>


}
fn main() {}