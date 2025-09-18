// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed string length access by using sequence view */
fn center_one(s: String, w: usize, c: char) -> (result: String)
    ensures 
        result@.len() as int == if s@.len() as int >= w as int { s@.len() as int } else { w as int },
        s@.len() as int >= w as int ==> result == s
{
    if s@.len() >= w {
        s
    } else {
        let total_pad = w - s@.len();
        let left_pad = total_pad / 2;
        let right_pad = total_pad - left_pad;
        let left_string = c.to_string().repeat(left_pad);
        let right_string = c.to_string().repeat(right_pad);
        let mut result = String::new();
        result.push_str(&left_string);
        result.push_str(&s);
        result.push_str(&right_string);
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper function with fixed string length access */
    let mut result = Vec::new();
    for i in 0..a.len() {
        let s = center_one(a[i], width[i], fillchar);
        result.push(s);
    }
    result
}
// </vc-code>

}
fn main() {}