// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(values: Seq<int>) -> bool {
    values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
}

spec fn gcd(a: int, b: int) -> int
    decreases (if a >= b { a } else { b }) when a > 0 && b > 0
{
    if a > 0 && b > 0 {
        if a == b {
            a
        } else if a > b {
            gcd(a - b, b)
        } else {
            gcd(a, b - a)
        }
    } else {
        1
    }
}

spec fn gcd_seq(values: Seq<int>, index: int, current: int) -> int
    decreases values.len() - index when 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
{
    if 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        if index == values.len() {
            current
        } else {
            gcd_seq(values, index + 1, gcd(current, values[index as int]))
        }
    } else {
        1
    }
}

spec fn gcd_of_all(values: Seq<int>) -> int {
    if values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        gcd_seq(values, 1, values[0])
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn values_as_int(values: Seq<i8>) -> Seq<int> {
    values.map(|i, x| x as int)
}

proof fn gcd_seq_decreases(values: Seq<int>, index: int, current: int)
    requires
        0 <= index <= values.len(),
        current > 0,
        forall|i: int| 0 <= i < values.len() ==> values[i] > 0;
    ensures values.len() - index >= 0;
{
    if index < values.len() {
        gcd_seq_decreases(values, index + 1, gcd(current, values[index]));
    }
}

/* helper modified by LLM (iteration 5): Fixed compilation error with proper condition syntax */
proof fn gcd_seq_decreases_fixed(values: Seq<int>, index: int, current: int)
    requires
        0 <= index <= values.len(),
        current > 0,
        forall|i: int| 0 <= i < values.len() ==> values[i] > 0;
    ensures values.len() - index >= 0;
{
    if index < values.len() {
        gcd_seq_decreases_fixed(values, index + 1, gcd(current, values[index]));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(values: Vec<i8>) -> (result: i8)
    requires valid_input(values_as_int(values@)) && values.len() <= 127
    ensures 
        result > 0 &&
        result as int == gcd_of_all(values_as_int(values@)) &&
        forall|i: int| 0 <= i < values@.len() ==> (values@[i] as int) % (result as int) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error with proper condition syntax */
    let mut result_int: int = values@[0] as int;
    let mut idx: usize = 1;
    
    while idx < values.len()
        invariant
            idx >= 1,
            idx <= values.len(),
            result_int > 0,
            result_int == gcd_seq(values_as_int(values@), idx as int, values@[0] as int),
            forall|i: int| 0 <= i < idx as int ==> (values@[i] as int) % result_int == 0;
        decreases values.len() - idx;
    {
        let prev_result = result_int;
        let current_val = values@[idx] as int;
        
        proof {
            gcd_seq_decreases_fixed(values_as_int(values@), idx as int, prev_result);
        }
        
        let mut a = prev_result;
        let mut b = current_val;
        
        while a != b
            invariant
                a > 0,
                b > 0,
                gcd(a, b) == gcd(prev_result, current_val),
                forall|i: int| 0 <= i < idx as int ==> (values@[i] as int) % a == 0,
                current_val % b == 0;
            decreases a + b;
        {
            if a > b {
                a = a - b;
            } else {
                b = b - a;
            }
        }
        
        result_int = a;
        idx = idx + 1;
    }
    
    result_int as i8
}
// </vc-code>


}

fn main() {}