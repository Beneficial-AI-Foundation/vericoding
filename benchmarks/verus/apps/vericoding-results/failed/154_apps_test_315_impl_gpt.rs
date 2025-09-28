// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool
{
    n >= 1 && a.len() == n && k >= 0 && forall|i: int| 0 <= i < n ==> #[trigger] a[i] >= 0
}

spec fn valid_output(a: Seq<int>, final_schedule: Seq<int>, additional_walks: int, k: int) -> bool
{
    final_schedule.len() == a.len() &&
    additional_walks >= 0 &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] final_schedule[i] >= a[i] &&
    forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] final_schedule[i] + final_schedule[i + 1] >= k &&
    additional_walks == sum(final_schedule) - sum(a)
}
// </vc-preamble>

// <vc-helpers>
spec fn imax(x: int, y: int) -> int { if x < y { y } else { x } }

fn max_i8(x: i8, y: i8) -> (res: i8)
    ensures
        res as int == imax(x as int, y as int),
        res >= x,
        res >= y,
{
    if x < y { y } else { x }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, Vec<i8>))
    requires valid_input(n as int, k as int, a@.map_values(|x: i8| x as int))
    ensures valid_output(a@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int), result.0 as int, k as int)
// </vc-spec>
// <vc-code>
{
    let n_usize = a.len();
    let mut b: Vec<i8> = Vec::with_capacity(n_usize);
    let mut i: usize = 0;
    let mut add: int = 0;

    while i < n_usize
        invariant
            b.len() == i,
            0 <= i <= n_usize,
            add == sum(b@.map_values(|x: i8| x as int)) - sum(a@.map_values(|x: i8| x as int).subrange(0, i as int)),
            forall|j: int| 0 <= j < i as int ==> (b@.map_values(|x: i8| x as int))[j] >= (a@.map_values(|x: i8| x as int))[j],
            forall|j: int| 0 <= j < i as int ==> (b@.map_values(|x: i8| x as int))[j] >= k as int,
        decreases (n_usize - i) as int
    {
        let ai = a[i];
        let bi = max_i8(ai, k);
        add = add + (bi as int - ai as int);
        b.push(bi);
        i = i + 1;
    }

    // After the loop, b has the same length as a, and each b[j] >= a[j] and >= k
    // Prove adjacency condition using the facts b[j] >= k and k >= 0
    proof {
        assert(forall|j: int|
            0 <= j < b@.len() - 1 ==> (
                (b@.map_values(|x: i8| x as int))[j] + (b@.map_values(|x: i8| x as int))[j + 1] >= k as int
            )) by {
            assert(forall|j: int|
                0 <= j < b@.len() ==> (b@.map_values(|x: i8| x as int))[j] >= k as int);
            assert(forall|j: int|
                0 <= j < b@.len() ==> (b@.map_values(|x: i8| x as int))[j] >= 0) by {
                assert(k as int >= 0);
            };
        };
    }

    let additional_i8: i8 = add as i8;
    (additional_i8, b)
}
// </vc-code>


}

fn main() {}