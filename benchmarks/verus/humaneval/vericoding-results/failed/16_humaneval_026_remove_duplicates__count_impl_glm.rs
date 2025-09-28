// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1 as int } else { 0 as int })
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed ghost variable, changed cnt to int, fixed braces */
    let mut cnt: int = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            cnt == count_rec(a@.map(|i: int, v: i8| v as int).subrange(0, i as int), x as int),
        decreases (a.len() - i) as int
    {
        if a[i] == x {
            cnt += 1;
        }
        i += 1;
    }
    cnt as i8
}
// </vc-code>


}

fn main() {}