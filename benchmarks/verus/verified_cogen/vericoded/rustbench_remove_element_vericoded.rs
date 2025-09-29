// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic min helper for ints */
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }

/* helper modified by LLM (iteration 5): check index within range 0..n */
spec fn in_range(i: int, n: int) -> bool { 0 <= i && i < n }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires
        0 <= pos < a.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove element by copying prefix then suffix; maintain sequence invariants with correct int/nat casts */
    let n = a.len();
    let mut v: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < pos
        invariant
            0 <= i as int,
            i <= pos,
            pos < a.len(),
            v.len() == i,
            i as int <= a@.len() as int,
            v@ == a@.take(i as int),
        decreases (pos as int - i as int)
    {
        v.push(a[i]);
        i += 1;
    }

    let mut i2: usize = pos + 1;

    proof {
        assert(a@.subrange(pos as int + 1, pos as int + 1) == Seq::<i32>::empty());
        assert(v@ == a@.take(pos as int));
        assert(v@ == a@.take(pos as int) + a@.subrange(pos as int + 1, pos as int + 1));
    }

    while i2 < n
        invariant
            n == a.len(),
            0 <= pos as int,
            pos < n,
            pos + 1 <= i2,
            i2 <= n,
            pos as int + 1 <= i2 as int,
            i2 as int <= a@.len() as int,
            v.len() == i2 - 1,
            v@ == a@.take(pos as int) + a@.subrange(pos as int + 1, i2 as int),
        decreases (n as int - i2 as int)
    {
        v.push(a[i2]);
        i2 += 1;
    }

    proof {
        assert(i2 == n);
        assert(v@ == a@.take(pos as int) + a@.subrange(pos as int + 1, n as int));
        assert(v.len() as int == a@.len() as int - 1);
        assert(forall|i:int| 0 <= i && i < pos as int ==> v@[i] == a@[i]);
        assert(forall|i:int| pos as int <= i && i < v.len() as int ==> v@[i] == a@[i + 1]);
    }

    v
}
// </vc-code>

}
fn main() {}