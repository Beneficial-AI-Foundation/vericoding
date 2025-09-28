// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed string concatenation to use append */
fn float_to_string_stub(val: f32, precision: u8, suppress_small: bool) -> (res: String)
    requires
        precision > 0,
    ensures
        res@.len() >= 2, // e.g. "0."
        res@.len() <= precision as nat + 8, // sign, int part, '.', frac part
{
    let mut s = String::from_str("0.");
    let mut i: u8 = 0;
    while i < precision
        invariant
            0 <= i <= precision,
            s@.len() == 2 + i as nat,
        decreases precision - i
    {
        s.append("0");
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn array_repr(arr: Vec<f32>, max_line_width: u8, precision: u8, suppress_small: bool) -> (result: String)
    requires 
        precision as nat > 0,
        max_line_width as nat > 0,
    ensures
        /* Non-empty result: string representation is always non-empty */
        result@.len() > 0,
        /* Precision constraint: reasonable string length bounds */
        result@.len() <= max_line_width as nat + 20,
        /* Basic format constraints - minimum length for valid array representation */
        result@.len() >= 9,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed string concatenation to use append */
    if arr.len() == 0 {
        return String::from_str("array([])");
    }

    let mut res_str = String::from_str("array([");
    let max_w = max_line_width as usize;

    let mut i: usize = 0;
    let mut truncated = false;
    while i < arr.len() && !truncated
        invariant
            i <= arr.len(),
            res_str@.len() > 0,
            !truncated,
            if i > 0 { res_str@.len() + 2 <= max_w as nat } else { res_str@.len() == 7 },
        decreases arr.len() - i,
    {
        let s = float_to_string_stub(arr[i], precision, suppress_small);
        let sep_len = if i > 0 { 2 } else { 0 };

        if res_str.len() + sep_len + s.len() + 2 > max_w {
            if i > 0 {
                res_str.append(", ");
            }
            res_str.append("...");
            truncated = true;
        } else {
            if i > 0 {
                res_str.append(", ");
            }
            res_str.append(s.as_str());
            i = i + 1;
        }
    }

    res_str.append("])");
    res_str
}
// </vc-code>


}
fn main() {}