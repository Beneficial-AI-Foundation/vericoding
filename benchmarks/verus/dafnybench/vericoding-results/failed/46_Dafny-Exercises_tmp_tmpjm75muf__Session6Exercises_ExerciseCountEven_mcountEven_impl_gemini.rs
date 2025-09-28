// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): reviewed and confirmed inductive proof structure */
proof fn count_even_append(s1: Seq<int>, s2: Seq<int>)
    requires
        positive(s1),
        positive(s2),
    ensures
        count_even(s1.add(s2)) == count_even(s1) + count_even(s2),
    decreases s2.len()
{
    if s2.len() > 0 {
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        count_even_append(s1, s2_prefix);
    }
}
// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error and added proof block for invariant */
    let mut n: i32 = 0;
    let mut i: usize = 0;
    let ghost s = v@.map(|_i: int, x: i32| x as int);
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(s),
            n as int == count_even(s.subrange(0, i as int)),
            s === v@.map(|_i: int, x: i32| x as int),
        decreases v.len() - i
    {
        proof {
            let s_prefix = s.subrange(0, i as int);
            let s_one = seq![s[i as int]];
            count_even_append(s_prefix, s_one);
        }

        if v[i] % 2 == 0 {
            n = n + 1;
        }
        i = i + 1;
    }
    n
}
// </vc-code>

}
fn main() {}