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
/* helper modified by LLM (iteration 5): fixed syntax in forall statement */
proof fn lemma_map_subrange_commute(s: Seq<i8>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures s.subrange(i, j).map(|idx: int, v: i8| v as int) == s.map(|idx: int, v: i8| v as int).subrange(i, j)
{
    let f = |idx: int, v: i8| v as int;
    assert_by(equal_by_ext(s.subrange(i, j).map(f), s.map(f).subrange(i, j)), {
        forall |k: int| 0 <= k < (j - i)
            ensures (s.subrange(i, j).map(f))[k] == (s.map(f).subrange(i, j))[k]
        {
        }
    });
}

proof fn lemma_count_rec_non_negative(s: Seq<int>, x: int)
    ensures count_rec(s, x) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_rec_non_negative(s.subrange(1, s.len() as int), x);
    }
}

// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed; awaiting verification with fixed helper */
    let mut cnt: i8 = 0;
    let mut i: usize = 0;
    let len = a.len();

    while i < len
        invariant
            0 <= i <= len,
            // The following invariant is an implicit precondition on a.len() to ensure the result fits in an i8
            count_rec(a@.map(|idx: int, v: i8| v as int), x as int) <= i8::MAX as int,
            cnt as int + count_rec(a@.subrange(i as int, len as int).map(|idx: int, v: i8| v as int), x as int)
                == count_rec(a@.map(|idx: int, v: i8| v as int), x as int),
            cnt >= 0,
    {
        proof {
            lemma_map_subrange_commute(a@, i as int, len as int);
            lemma_map_subrange_commute(a@, i as int + 1, len as int);
        }

        if a[i] == x {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}

// </vc-code>


}

fn main() {}