// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed ensures from spec function to fix compilation */
spec fn abs_i8(v: i8) -> int {
    let val = v as int;
    if val >= 0 { val } else { -val }
}

/* helper modified by LLM (iteration 4): removed ensures from spec function to fix compilation */
spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 3): no changes, just fixing code section based on errors */
fn abs_i8_exec(v: i8) -> (res: i16)
    ensures
        res >= 0,
        res as int == abs_i8(v),
        res <= 128,
{
    let v_i16 = v as i16;
    if v_i16 >= 0 { v_i16 } else { -v_i16 }
}

/* helper modified by LLM (iteration 2): added executable max helper */
fn max_i16(a: i16, b: i16) -> (res: i16)
    ensures
        res >= a,
        res >= b,
        res == a || res == b,
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn condition_number(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x.len(),
    ensures 
        result as int >= 0,
        result as int >= 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Strengthened inner loop invariants to fix precondition failure. */
    let n = x.len();
    let mut max_abs_val: i16 = 0;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            x.len() == n,
            forall|k: int| 0 <= k < n as int ==> x@[k].len() == n as int,
            max_abs_val >= 0,
            max_abs_val <= 128,
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==> abs_i8(x@[r]@[c]) <= max_abs_val as int,
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < n,
                0 <= j <= n,
                x.len() == n,
                forall|k: int| 0 <= k < n as int ==> x@[k].len() == n as int,
                max_abs_val >= 0,
                max_abs_val <= 128,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==> abs_i8(x@[r]@[c]) <= max_abs_val as int,
                forall|c: int| 0 <= c < j as int ==> abs_i8(x@[i as int]@[c]) <= max_abs_val as int,
            decreases n - j
        {
            let val = abs_i8_exec(x[i][j]);
            max_abs_val = max_i16(max_abs_val, val);
            j = j + 1;
        }
        i = i + 1;
    }

    let result = if max_abs_val < 127 {
        (max_abs_val + 1) as i8
    } else {
        127
    };
    
    result
}
// </vc-code>


}
fn main() {}