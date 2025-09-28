// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_odd_at_even_positions(lst: Seq<int>, pos: int) -> int
    decreases if pos < lst.len() { lst.len() - pos } else { 0 }
{
    if pos >= lst.len() {
        0
    } else if lst[pos] % 2 == 1 {
        lst[pos] + sum_odd_at_even_positions(lst, pos + 2)
    } else {
        sum_odd_at_even_positions(lst, pos + 2)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_rem_euclid_is_mod_one(x: i8)
    ensures
        ((x as int) % 2 == 1) <==> (x.rem_euclid(2) == 1),
{
    vstd::arithmetic::div_mod::lemma_rem_euclid_int_is_rem_euclid_i8(x, 2);
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    let s = lst@.map(|_i: int, x: i8| x as int);

    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            i % 2 == 0,
            sum as int == sum_odd_at_even_positions(s, 0) - sum_odd_at_even_positions(s, i as int),
        decreases lst.len() - i
    {
        let x = lst[i];
        lemma_rem_euclid_is_mod_one(x);
        if x.rem_euclid(2) == 1 {
            sum = sum + x as i64;
        }
        i = i + 2;
    }

    let total_sum_spec = sum_odd_at_even_positions(s, 0);
    assert(sum as int == total_sum_spec);

    assert(i8::MIN as int <= total_sum_spec && total_sum_spec <= i8::MAX as int);
    vstd::arithmetic::casting::lemma_i64_as_int_in_range_means_i64_in_range(sum, i8::MIN as int, i8::MAX as int);

    sum as i8
}
// </vc-code>


}

fn main() {}