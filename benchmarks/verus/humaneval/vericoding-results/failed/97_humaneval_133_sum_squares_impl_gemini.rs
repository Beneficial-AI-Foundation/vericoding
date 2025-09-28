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
proof fn lemma_sum_of_add(s1: Seq<int>, s2: Seq<int>)
    ensures sum(s1.add(s2)) == sum(s1) + sum(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_sum_of_add(s1.subrange(1, s1.len() as int), s2);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (r: i8)
    ensures r as int == sum(square_seq(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation errors by using ghost context and appropriate integer types */
    let mut total: i64 = 0;
    let mut i: usize = 0;

    ghost let s_int = lst@.map(|_idx: int, x: i8| x as int);
    ghost let target_seq = square_seq(s_int);

    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            s_int === lst@.map(|_idx: int, x: i8| x as int),
            target_seq === square_seq(s_int),
            total as int == sum(target_seq.subrange(0, i as int)),
    {
        let x_i8 = lst[i];
        let x_i64 = x_i8 as i64;
        let val_to_add = (x_i64 + 1) * (x_i64 + 1);

        proof {
            let processed = target_seq.subrange(0, i as int);
            let next_item_seq = target_seq.subrange(i as int, (i + 1) as int);
            assert(val_to_add as int == next_item_seq[0]);
            assert(sum(next_item_seq) == next_item_seq[0]);
            lemma_sum_of_add(processed, next_item_seq);
        }

        total = total + val_to_add;
        i = i + 1;
    }

    total as i8
}
// </vc-code>


}

fn main() {}