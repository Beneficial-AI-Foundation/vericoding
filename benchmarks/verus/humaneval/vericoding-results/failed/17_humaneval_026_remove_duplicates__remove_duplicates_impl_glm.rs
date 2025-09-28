// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}
/* helper modified by LLM (iteration 5): fixed filter closure parameter type */
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < a@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) >= 1
    ensures 
        forall|i: int| 0 <= i < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[i] as int) == 1,
        forall|i: int| 0 <= i < a@.len() ==> (result@.map(|_i: int, x: i8| x as int).contains(a@[i] as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) == 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed filter closure to take single value parameter and correct type */
    let mut result = Vec::new();
    let len = a.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result@ == a@.subrange(0, i as int).filter(|val: int| count_rec(a@.map(|y| y as int), val) == 1)
        decreases len - i
    {
        let x = a[i];
        let mut count: usize = 0;
        let mut j = 0;
        while j < len
            invariant
                0 <= j as int <= len as int,
                count as int == count_rec(a@.subrange(0, j as int).map(|_k: int, y: i8| y as int), x as int)
            decreases len - j
        {
            if a[j] == x {
                count += 1;
            }
            j += 1;
        }
        if count == 1 {
            result.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}