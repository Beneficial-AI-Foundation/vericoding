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
proof fn lemma_unfold_sum(lst: Seq<int>, pos: int)
    ensures
        sum_odd_at_even_positions(lst, pos)
            == if pos >= lst.len() { 0 } else if lst[pos] % 2 == 1 { lst[pos] + sum_odd_at_even_positions(lst, pos + 2) } else { sum_odd_at_even_positions(lst, pos + 2) },
{
    reveal_with_fuel(sum_odd_at_even_positions, 1);
}

proof fn lemma_sum_base_zero(lst: Seq<int>, pos: int)
    requires
        pos >= lst.len(),
    ensures
        sum_odd_at_even_positions(lst, pos) == 0,
{
    reveal_with_fuel(sum_odd_at_even_positions, 1);
}
// </vc-helpers>

// <vc-spec>
fn solution(lst: Vec<i8>) -> (result: i8)
    requires lst@.len() > 0
    ensures result as int == sum_odd_at_even_positions(lst@.map(|i: int, x: i8| x as int), 0)
// </vc-spec>
// <vc-code>
{
    let n = lst.len();
    let ghost s: Seq<int> = lst@.map(|i: int, x: i8| x as int);

    let mut i: usize = 0;
    let mut acc: int = 0;

    while i < n
        invariant
            n == lst.len(),
            i <= n,
            i % 2 == 0,
            acc + sum_odd_at_even_positions(s, i as int) == sum_odd_at_even_positions(s, 0),
        decreases n - i
    {
        proof { lemma_unfold_sum(s, i as int); }
        let xi = lst[i];
        if (xi as int) % 2 == 1 {
            acc = acc + (xi as int);
        }
        i = i + 2;
    }

    if i as int >= s.len() as int {
        proof { lemma_sum_base_zero(s, i as int); }
    }

    let result = acc as i8;
    result
}
// </vc-code>


}

fn main() {}