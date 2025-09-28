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
/* helper modified by LLM (iteration 5): lemma for count_rec on subrange step */
proof fn count_rec_subrange_step(s: Seq<int>, i: nat, n: nat, x: int)
    requires
        i < n,
        n <= s.len(),
    ensures
        count_rec(s.subrange(i, n), x) == (if s@[i] == x { 1 as int } else { 0 as int }) + count_rec(s.subrange(i + 1, n), x),
{
    proof {
        let t = s.subrange(i, n);
        assert(t.len() > 0);
        assert(count_rec(t, x) == (if t.len() == 0 { 0 as int } else { count_rec(t.subrange(1 as nat, t.len()), x) + (if t@[0] == x { 1 as int } else { 0 as int }) }));
        assert(count_rec(t, x) == count_rec(t.subrange(1 as nat, t.len()), x) + (if t@[0] == x { 1 as int } else { 0 as int }));
        assert(t@[0] == s@[i]);
        assert(t.subrange(1 as nat, t.len()) == s.subrange(i + 1, n));
    }
}

// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): count elements with loop and tracked invariant */
{
    let n = a.len();
    let mut i: usize = 0;
    let tracked mut cnt: i8 = 0;
    while i < n
        invariant
            cnt as int + count_rec(a@.map(|_: int, v: i8| v as int).subrange(i as nat, n as nat), x as int) == count_rec(a@.map(|_: int, v: i8| v as int), x as int),
        decreases n - i
    {
        let cur: i8 = a[i];
        if cur == x {
            cnt = cnt + 1;
        }
        i = i + 1;
        proof {
            let prev: nat = (i - 1) as nat;
            count_rec_subrange_step(a@.map(|_: int, v: i8| v as int), prev, n as nat, x as int);
        }
    }
    cnt
}

// </vc-code>


}

fn main() {}