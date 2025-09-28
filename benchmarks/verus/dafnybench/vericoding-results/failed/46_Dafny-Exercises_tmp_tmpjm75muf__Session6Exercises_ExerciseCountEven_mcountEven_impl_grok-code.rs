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

// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let tracked ptr: Seq<int> = v@.map(|_, x: i32| x as int);

    proof! {
        assert forall|i: int| 0 <= i < ptr.len() implies ptr[i] >= 0 by {
            assert(v@[i] >= 0);  // from precondition
            assert(ptr[i] == v@[i] as int);
        }
    }

    let mut count: i32 = 0;
    let len = v.len();

    for idx in 0..len
        invariant
            0 <= (idx as int) <= (len as int),
            count as int == count_even(ptr.subrange(0, idx as int))
    {
        proof! {
            let i: int = idx as int;
            assert(0 <= i < ptr.len());
            assert(v@[i] as int == ptr[i]);
            // Relate exec % to spec % (safe since v@[i] >= 0 from positive)
            assert(v@[i] as int % 2 == 0 <==> (v@[i] % 2 == 0));
            assert(ptr[i] % 2 == 0 <==> (ptr[i] % 2 == 0));
        }

        if v[idx] % 2 == 0 {
            proof! {
                let i: int = idx as int;
                assert(v@[i] as int == ptr[i]);
                assert(ptr[i] % 2 == 0);
            }
            count += 1;
        } else {
            proof! {
                let i: int = idx as int;
                assert(v@[i] as int == ptr[i]);
                assert(ptr[i] % 2 != 0);
            }
        }

        proof! {
            let i: int = idx as int;
            assert(ptr.subrange(0, i + 1) == ptr.subrange(0, i).push(ptr[i]));
            assert(count_even(ptr.subrange(0, i + 1)) == (if ptr[i] % 2 == 0 { 1 } else { 0 }) + count_even(ptr.subrange(0, i)));
        }
    }

    count
}
// </vc-code>

fn main() {
}

}