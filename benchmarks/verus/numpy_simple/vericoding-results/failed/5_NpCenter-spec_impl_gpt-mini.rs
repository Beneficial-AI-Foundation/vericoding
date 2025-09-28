// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create String of n spaces */
fn spaces_str(n: usize) -> String {
    let mut s = String::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i
    {
        s.push(' ');
        i += 1;
    }
    s
}

/* helper modified by LLM (iteration 5): center a single line into width */
fn center_line(s: String, width: usize) -> String
    requires
        s@.len() >= 1,
{
    let slen = s@.len() as usize;
    if slen > width {
        s
    } else {
        let diff = width - slen;
        let start = (diff + 1) / 2;
        let end = diff - start;
        let pre = spaces_str(start);
        let suf = spaces_str(end);
        let mut res = String::with_capacity(width);
        res.push_str(&pre);
        res.push_str(&s);
        res.push_str(&suf);
        res
    }
}

// </vc-helpers>

// <vc-spec>
fn center(input: Vec<String>, width: usize) -> (result: Vec<String>)
    requires 
        input.len() > 0,
        forall|i: int| 0 <= i < input.len() ==> input[i]@.len() >= 1,
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() > width {
                result[i]@.len() == input[i]@.len()
            } else {
                result[i]@.len() == width
            },
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() < width {
                let start_pos = (width - input[i]@.len() + 1) / 2;
                result[i]@.skip(start_pos as int).take(input[i]@.len() as int) == input[i]@
            } else {
                true
            }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement center using center_line */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            result.len() == i,
        decreases input.len() - i
    {
        let s = input[i].clone();
        let new_s = center_line(s, width);
        result.push(new_s);
        i += 1;
    }
    result
}

// </vc-code>


}
fn main() {}