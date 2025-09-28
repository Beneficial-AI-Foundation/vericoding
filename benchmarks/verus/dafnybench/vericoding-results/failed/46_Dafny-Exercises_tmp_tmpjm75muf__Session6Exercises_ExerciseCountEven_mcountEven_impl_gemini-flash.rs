use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_even(i: int) -> bool
    recommends i >= 0
{
    i % 2 == 0
}

spec fn count_even(s: Seq<int>) -> int
    recommends positive(s)
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[s.len() - 1] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(s.subrange(0, s.len() - 1))
    }
}

// <vc-helpers>
#[verifier(external_body)]
fn is_even_i32(i: i32) -> (b: bool)
    ensures b == is_even(i as int)
{
    i % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let mut count: i32 = 0;
    let mut i: usize = 0;

    while i < v.len()
        invariant
            0 <= i && i <= v.len(),
            count as int == count_even(v@.map(|k: int, x: i32| x as int).subrange(0, i as int)),
            positive(v@.map(|k: int, x: i32| x as int))
    {
        let val: i32 = v.view_nth(i);
        if is_even_i32(val) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

fn main() {
}

}