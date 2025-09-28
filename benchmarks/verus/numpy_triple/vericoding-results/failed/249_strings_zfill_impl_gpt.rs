// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a vector with n zeros */
fn zeros_vec(n: usize) -> (v: Vec<char>)
    ensures
        v.len() == n,
        all_zeros(v@),
{
    let mut v: Vec<char> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            v.len() == k,
            k <= n,
            forall|h: int| 0 <= h < v.len() ==> #[trigger] v@[h] == '0',
        decreases n - k
    {
        v.push('0');
        k += 1;
    }
    v
}

/* helper modified by LLM (iteration 5): left-pad a vector with `pad` zeros and append the original characters */
fn left_pad_with_zeros(s: Vec<char>, pad: usize) -> (v: Vec<char>)
    ensures
        v.len() == pad + s.len(),
        all_zeros(v@.take(pad as int)),
        v@.skip(pad as int) == s@,
{
    let mut v = zeros_vec(pad);
    let mut t = s.clone();
    v.append(&mut t);
    v
}
// </vc-helpers>

// <vc-spec>
spec fn is_sign_char(c: char) -> bool {
    c == '+' || c == '-'
}

spec fn all_zeros(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn zfill(a: Vec<Vec<char>>, width: usize) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i].len() == max_usize(a[i].len(), width),
        forall|i: int| 0 <= i < result.len() && a[i].len() >= width ==> 
            #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            !is_sign_char(a[i]@[0]) ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int)) &&
            result[i]@.skip((width - a[i].len()) as int) == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            is_sign_char(a[i]@[0]) ==> 
            #[trigger] result[i]@[0] == a[i]@[0] &&
            result[i]@.skip(width as int) == a[i]@.skip(1),
        forall|i: int| 0 <= i < result.len() && a[i].len() == 0 ==> 
            #[trigger] result[i].len() == width && 
            all_zeros(result[i]@),
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] result[i].len() == width,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace spec fn call with exec char check for sign */
    let mut res: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < i && a[j].len() >= width ==> #[trigger] res[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() == 0 ==> #[trigger] res[j].len() == width && all_zeros(res[j]@),
            forall|j: int| 0 <= j < i && a[j].len() < width ==> #[trigger] res[j].len() == width,
            forall|j: int| 0 <= j < i && a[j].len() < width ==> #[trigger] all_zeros(res[j]@.take((width - a[j].len()) as int)),
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && !is_sign_char(a[j]@[0]) ==> #[trigger] res[j]@.skip((width - a[j].len()) as int) == a[j]@,
        decreases a.len() - i
    {
        let s = a[i].clone();
        let s_len = s.len();
        if s_len >= width {
            res.push(s);
        } else {
            if s_len == 0 {
                let z = zeros_vec(width);
                res.push(z);
            } else {
                let pad: usize = width - s_len;
                if !(s[0] == '+' || s[0] == '-') {
                    let v = left_pad_with_zeros(s.clone(), pad);
                    res.push(v);
                } else {
                    let v = left_pad_with_zeros(s.clone(), pad);
                    res.push(v);
                }
            }
        }
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}