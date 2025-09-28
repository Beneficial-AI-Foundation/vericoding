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
/* helper modified by LLM (iteration 5): convert nat count to u8 by incrementing */
fn count_to_u8(count: nat) -> (result: u8)
    ensures
        result as nat == count,
{
    let mut r: u8 = 0;
    let mut rem: nat = count;
    while rem > 0 as nat
        invariant
            r as nat + rem == count,
        decreases rem
    {
        r = r + 1;
        rem = rem - (1 as nat);
    }
    r
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
{
    /* code modified by LLM (iteration 5): return unit and count as u8 using helper */
    match dtype {
        DatetimeDtype::Datetime64(info) => {
            let unit = info.unit;
            let cnt: u8 = count_to_u8(info.count);
            (unit, cnt)
        }
        DatetimeDtype::Timedelta64(info) => {
            let unit = info.unit;
            let cnt: u8 = count_to_u8(info.count);
            (unit, cnt)
        }
    }
}
// </vc-code>


}
fn main() {}