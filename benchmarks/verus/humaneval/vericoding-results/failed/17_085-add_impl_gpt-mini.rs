// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): step lemma to expand add_odd_evens at position k*2 */
proof fn add_odd_evens_step(s: Seq<u32>, k: nat)
    requires
        k * 2 + 1 < s.len(),
    ensures
        add_odd_evens(s.skip((k * 2) as nat)) == (odd_or_zero(s[(k * 2 + 1) as nat]) as int) + add_odd_evens(s.skip(((k + 1) * 2) as nat)),
    decreases
        s.len() - (k * 2)
{
    let t = s.skip((k * 2) as nat);
    assert(t.len() >= 2);
    assert(add_odd_evens(t) == (odd_or_zero(t[1]) as int) + add_odd_evens(t.skip(2)));
    assert(t[1] == s[(k * 2 + 1) as nat]);
    assert(t.skip(2) == s.skip(((k + 1) * 2) as nat));
}

/* helper modified by LLM (iteration 5): non-negativity of add_odd_evens */
proof fn add_odd_evens_nonneg(lst: Seq<u32>)
    ensures
        add_odd_evens(lst) >= 0,
    decreases
        lst.len(),
{
    if lst.len() < 2 {
    } else {
        add_odd_evens_nonneg(lst.skip(2));
        assert(add_odd_evens(lst.skip(2)) >= 0);
        assert((odd_or_zero(lst[1]) as int) + add_odd_evens(lst.skip(2)) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate odd indices and maintain invariant linking acc and spec sum */
    let s = lst@;
    let mut pos: usize = 0;
    let mut acc: u64 = 0;
    while pos * 2 + 1 < lst.len()
        invariant
            (acc as int) + add_odd_evens(s.skip((pos * 2) as nat)) == add_odd_evens(s),
        decreases
            s.len() - ((pos * 2) as nat)
    {
        let idx = pos * 2 + 1;
        let val = lst[idx];
        if val % 2 == 0 {
            acc = acc + (val as u64);
        }
        proof {
            assert(s[idx as nat] == val);
            add_odd_evens_step(s, pos as nat);
            assert(add_odd_evens(s.skip((pos * 2) as nat)) == (odd_or_zero(s[(pos * 2 + 1) as nat]) as int) + add_odd_evens(s.skip(((pos + 1) * 2) as nat)));
            if val % 2 == 0 {
                assert(odd_or_zero(s[(pos * 2 + 1) as nat]) as int == (val as int));
            } else {
                assert(odd_or_zero(s[(pos * 2 + 1) as nat]) == 0);
            }
        }
        pos = pos + 1;
    }
    proof {
        assert(!(pos * 2 + 1 < lst.len()));
        assert(s.skip((pos * 2) as nat).len() < 2);
        assert(add_odd_evens(s.skip((pos * 2) as nat)) == 0);
        assert((acc as int) + 0 == add_odd_evens(s));
    }
    acc
}
// </vc-code>

}
fn main() {}