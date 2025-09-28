// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helpers are correct */
spec fn prefix_sum(s: Seq<i8>, i: int) -> int
    recommends 0 <= i < s.len()
    decreases i
{
    if i == 0 {
        s[0] as int
    } else {
        prefix_sum(s, i - 1) + s[i] as int
    }
}

spec fn is_i8_int(v: int) -> bool {
    i8::MIN <= v && v <= i8::MAX
}
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using an executable integer type (i16) for the intermediate sum */
    let mut result = Vec::new();
    result.push(a[0]);

    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == prefix_sum(a@, j),
        decreases a.len() - i
    {
        let prev_val = result[(i - 1) as usize];
        let current_val = a[i as usize];
        
        let sum = prev_val as i16 + current_val as i16;
        let next_val = sum as i8;

        result.push(next_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}