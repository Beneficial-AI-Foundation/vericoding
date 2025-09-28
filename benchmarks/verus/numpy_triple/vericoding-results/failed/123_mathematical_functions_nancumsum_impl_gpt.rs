// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec addition for i8 values as ints */
pub open spec fn i8_add_as_int(x: i8, y: i8) -> int {
    x as int + y as int
}

/* helper modified by LLM (iteration 5): basic fact about usize ordering */
pub proof fn lt_implies_pos(i: usize, n: usize)
    ensures
        i < n ==> 0 < n,
{
}

// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cumulative sum with correct invariants over sequence bounds */
    let a_len: usize = a.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a_len
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            res.len() == i as int,
            i as int > 0 ==> 0 < a@.len(),
            i as int > 0 ==> res@[0] as int == a@[0] as int,
            forall|j: int| 0 < j < i as int ==> res@[j] as int == res@[(j - 1)] as int + a@[j] as int,
        decreases (a_len - i) as int
    {
        if i == 0 {
            proof { lt_implies_pos(i, a_len); }
            res.push(a[0]);
        } else {
            let prev: i8 = res[i - 1];
            let ai: i8 = a[i];
            let next: i8 = prev + ai;
            res.push(next);
        }
        proof {
            assert(a@.len() as int == a_len as int);
            assert(i as int < a_len as int);
            assert(i as int + 1 <= a_len as int);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}