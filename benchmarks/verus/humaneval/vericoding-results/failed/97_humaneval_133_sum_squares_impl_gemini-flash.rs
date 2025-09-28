// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn ceil(f: int) -> int {
    f + 1
}

spec fn square_seq(lst: Seq<int>) -> Seq<int> {
    Seq::new(lst.len(), |i: int| ceil(lst[i]) * ceil(lst[i]))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (r: i8)
    ensures r as int == sum(square_seq(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [cast `i` to int for indexing and use i64 for intermediate calculation to avoid overflow issues, then cast back to i8 for total] */
{
    let mut total: i64 = 0;
    let mut i: nat = 0;

    while i < lst.len()
        invariant
            0 <= i,
            i <= lst.len(),
            total as int == sum(square_seq(lst@.subrange(0, i as int).map(|j: int, x: i8| x as int))),

    {
        let val = lst[i as int];
        let term_i = (val as i64 + 1) * (val as i64 + 1);
        total = total + term_i;
        i = i + 1;
    }
    total as i8
}
// </vc-code>


}

fn main() {}