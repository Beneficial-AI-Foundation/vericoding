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
{
    /* helper modified by LLM (iteration 3): unroll lemma for sum_odd_at_even_positions */
    proof fn sum_odd_at_even_positions_unroll(seq: Seq<int>, pos: int)
        ensures
            sum_odd_at_even_positions(seq, pos) ==
                if pos >= seq.len() {
                    0
                } else if seq@[pos] % 2 == 1 {
                    seq@[pos] + sum_odd_at_even_positions(seq, pos + 2)
                } else {
                    sum_odd_at_even_positions(seq, pos + 2)
                },
    {
        reveal(sum_odd_at_even_positions);
        if pos >= seq.len() {
            assert(sum_odd_at_even_positions(seq, pos) == 0);
        } else {
            if seq@[pos] % 2 == 1 {
                assert(sum_odd_at_even_positions(seq, pos) == seq@[pos] + sum_odd_at_even_positions(seq, pos + 2));
            } else {
                assert(sum_odd_at_even_positions(seq, pos) == sum_odd_at_even_positions(seq, pos + 2));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterative sum of odd elements at even positions */
    let seq: Seq<int> = lst@.map(|_i: int, x: i8| x as int);
    let mut acc: int = 0;
    let mut i: nat = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            acc + sum_odd_at_even_positions(seq, i as int) == sum_odd_at_even_positions(seq, 0),
        decreases lst.len() - i
    {
        if seq@[i as int] % 2 == 1 {
            acc = acc + seq@[i as int];
        }
        i = i + 2;
    }
    let result: i8 = acc as i8;
    result
}
// </vc-code>


}

fn main() {}