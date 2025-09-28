// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using string_from_seq */
fn repeat_char(c: char, n: usize) -> (res: String)
    ensures
        res@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] res@[i] == c,
{
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            chars.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] chars@[j] == c,
        decreases n - i
    {
        chars.push(c);
        i = i + 1;
    }
    vstd::string::string_from_seq(chars@)
}

/* helper modified by LLM (iteration 4): implemented centering logic and used append instead of push_str */
fn center_string(s: &String, width: usize, fillchar: char) -> (res: String)
    ensures
        res@.len() as int == if s@.len() as int >= width as int { s@.len() as int } else { width as int },
        (s@.len() >= width) ==> res == *s,
{
    let orig_len = s.len();
    if orig_len >= width {
        s.clone()
    } else {
        let pad_len = width - orig_len;
        let left_pad_len = pad_len / 2;
        let right_pad_len = pad_len - left_pad_len;

        let left_padding = repeat_char(fillchar, left_pad_len);
        let right_padding = repeat_char(fillchar, right_pad_len);

        let mut result = left_padding;
        result.append(s.clone());
        result.append(right_padding);
        
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
    /* code modified by LLM (iteration 5): no changes, logic appears correct */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == width.len(),
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j]@.len() >= 0 && {
                    let orig_len = a[j]@.len() as int;
                    let target_width = width[j] as int;
                    &&& (orig_len >= target_width ==> result[j] == a[j])
                    &&& result[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
                },
        decreases a.len() - i 
    {
        let centered_s = center_string(&a[i], width[i], fillchar);
        result.push(centered_s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}