// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn repeat_char(fillchar: char, n: usize) -> (result: String)
    ensures 
        result@.len() == n as nat,
        forall |k: int| 0 <= k < result@.len() ==> result@[k] == fillchar
{
    let mut result = String::new();
    let mut i = 0;
    while i < n {
        invariant
            i >= 0,
            i <= n,
            result@.len() == i,
            forall |k: int| 0 <= k < i ==> result@[k] == fillchar
        ;
        result.push(fillchar);
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 5): fixed code to use @.len() directly instead of helper */
    let mut result: Vec<String> = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len() {
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as nat;
                let target = width[j] as nat;
                if orig_len >= target {
                    (result[j] == a[j]) && result[j]@.len() as nat == orig_len
                } else {
                    result[j]@.len() as nat == target
                }
            }
        ;
        let s = &a[i];
        let len = s@.len() as nat;
        let w = width[i] as nat;
        let pad_size = if w > len { (w - len) as usize } else { 0 };
        let pad_left = pad_size / 2;
        let pad_right = pad_size - pad_left;
        if pad_size == 0 {
            result.push(s.clone());
        } else {
            let left = repeat_char(fillchar, pad_left);
            let right = repeat_char(fillchar, pad_right);
            let mut new_s = left;
            new_s.push_str(&s.as_str());
            new_s.push_str(&right.as_str());
            result.push(new_s);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}