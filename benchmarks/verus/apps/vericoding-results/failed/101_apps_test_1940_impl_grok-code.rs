// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, w: Seq<int>) -> bool {
    k > 0 && n >= 0 && w.len() == n && forall|i: int| 0 <= i < w.len() ==> w[i] >= 0
}

spec fn sum_trips(w: Seq<int>, k: int) -> int
    decreases w.len()
{
    if w.len() == 0 {
        0
    } else {
        (w[0] + k - 1) / k + sum_trips(w.drop_first(), k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added requirement to ensure result fits in i32 to avoid truncation and potential overflow */
fn ceil_div(a: i32, b: i32) -> (result: i32)
    requires
        a >= 0,
        b > 0,
        (a as int + b as int - 1) / (b as int) <= i32::MAX as int,
    ensures
        result >= 0,
        result as int == (a as int + b as int - 1) / (b as int),
{
    let num: i64 = (a as i64) + (b as i64) - 1;
    let den: i64 = b as i64;
    (num / den) as i32
}

/* helper modified by LLM (iteration 5): removed assertions causing verification issues */
fn sum_trip_exec(w: &Vec<i8>, k: i8) -> (ret: i32)
    requires
        valid_input(w@.len() as int, k as int, w@.map_values(|v: i8| v as int)),
    ensures
        ret as int == sum_trips(w@.map_values(|v: i8| v as int), k as int),
        ret >= 0,
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < w.len()
        invariant
            0 <= i <= w.len(),
            sum as int == sum_trips(w@.map_values(|v: i8| v as int).take(i as int), k as int),
        decreases w.len() - i
    {
        sum = sum + ceil_div(w[i] as i32, k as i32);
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, w: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, w@.map_values(|v: i8| v as int)),
    ensures 
        result >= 0,
        result as int == (sum_trips(w@.map_values(|v: i8| v as int), k as int) + 1) / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added requirement to ensure result fits in i8 range */
{
    let sum = sum_trip_exec(&w, k);
    let s: i64 = sum as i64;
    let res_i32: i32 = ((s + 1) / 2) as i32;
    assert(res_i32 >= 0 && res_i32 <= 127);
    let result = (res_i32 as i8);
    result
}
// </vc-code>


}

fn main() {}