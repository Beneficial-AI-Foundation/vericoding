// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ensure result preserves prefix and has correct length */
fn pad_right(mut s: String, add: usize, fill: char) -> (res: String)
    ensures
        res.len() == s.len() + add,
        res@.len() == s@.len() + add as nat,
        res@.subrange(0, s@.len() as int) == s@,
{
    let mut r = s.clone();
    let mut i: usize = 0;
    while i < add
        invariant
            r.len() == s.len() + i,
            r@.len() == s@.len() + i as nat,
            r@.subrange(0, s@.len() as int) == s@,
        decreases add - i
    {
        r.push(fill);
        i = i + 1;
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn ljust(a: Vec<String>, width: u8, fillchar: char) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == if a[i]@.len() >= width as nat { a[i]@.len() } else { width as nat },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() >= width as nat ==> #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() && a[i]@.len() < width as nat ==> {
            &&& #[trigger] result[i]@.len() == width as nat
            &&& result[i]@.subrange(0, a[i]@.len() as int) == a[i]@
        },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == width as nat
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result and prove specs using pad_right; fix proof loop index types */
    let mut result: Vec<String> = Vec::<String>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
        decreases a.len() - i
    {
        let s = a[i].clone();
        let cur = s.len();
        if cur >= width as usize {
            result.push(s);
        } else {
            let add = width as usize - cur;
            let r = pad_right(s, add, fillchar);
            result.push(r);
        }
        i = i + 1;
    }

    proof {
        let mut j: int = 0;
        while j < a.len() as int
            invariant
                0 <= j && j <= a.len() as int,
            decreases a.len() as int - j
        {
            let s = a[j as usize].clone();
            if s@.len() >= width as nat {
                assert(result[j as usize]@ == s@);
                assert(result[j as usize]@.len() == s@.len());
            } else {
                assert(result[j as usize]@.len() == width as nat);
                assert(result[j as usize]@.subrange(0, s@.len() as int) == s@);
            }
            j = j + 1;
        }
    }

    result
}
// </vc-code>


}
fn main() {}