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
proof fn lemma_vec_map_index(v: &Vec<i32>, idx: int)
    requires 0 <= idx && idx < v.len() as int
    ensures v@.map(|j: int, x: i32| x as int)@[idx] == (v@)[idx] as int
{
    assert(v@.map(|j: int, x: i32| x as int)@[idx] == (v@)[idx] as int);
}

proof fn lemma_map_len(v: &Vec<i32>)
    ensures v@.map(|i: int, x: i32| x as int).len() as int == v.len() as int
{
    // The Seq produced by mapping has the same length as v@
    assert(v@.map(|i: int, x: i32| x as int).len() == v@.len());
    // v@.len() corresponds to v.len()
    assert(v@.len() as int == v.len() as int);
}
// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let s: Seq<int> = v@.map(|i: int, x: i32| x as int);

    let mut i: usize = 0;
    let mut acc: i32 = 0;

    // Loop over v, maintaining that acc equals count_even of the prefix of length i.
    while i < v.len()
        invariant 0 <= (i as int)
        invariant (i as int) <= (v.len() as int)
        invariant (acc as int) == count_even(s.subrange(0, i as int))
        decreases (v.len() as int - i as int)
    {
        let old_acc: i32 = acc;
        let x: i32 = v.index(i);

        // capture current prefix length as int
        let ii: int = i as int;

        // ensure ii is within bounds of v and s
        proof {
            // from loop invariant and loop guard
            assert(0 <= (i as int));
            assert((i as int) < (v.len() as int)); // because i < v.len()
            assert(ii == i as int);
            assert(0 <= ii && ii < v.len() as int);
            // relate lengths of v and s
            lemma_map_len(v);
            assert(v.len() as int == s.len() as int);
            assert(ii < s.len() as int);
        }

        if (x as int) % 2 == 0 {
            // prove that count_even(s.subrange(0, ii+1)) == 1 + count_even(s.subrange(0, ii))
            proof {
                let t = s.subrange(0, ii + 1);
                let tlen: int = t.len() as int;
                assert(tlen == ii + 1);
                assert(count_even(t) == (if t[tlen - 1] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(t.subrange(0, tlen - 1)));
                assert(t[tlen - 1] == s[ii]);
                assert(t.subrange(0, tlen - 1) == s.subrange(0, ii));
                assert(count_even(s.subrange(0, ii + 1)) == (if s[ii] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(s.subrange(0, ii)));
                // relate runtime element x to sequence element s@[ii]
                lemma_vec_map_index(v, ii);
                assert(s@[ii] == (v@)[ii] as int);
                assert((x as int) == s@[ii]);
                // loop invariant before update: old_acc as int == count_even(s.subrange(0, ii))
                assert(old_acc as int == count_even(s.subrange(0, ii)));
                // therefore 1 + old_acc == count_even(s.subrange(0, ii+1))
                assert((old_acc as int) + 1 == count_even(s.subrange(0, ii + 1)));
            }
            acc = old_acc + 1;
        } else {
            // prove that count_even(s.subrange(0, ii+1)) == 0 + count_even(s.subrange(0, ii))
            proof {
                let t = s.subrange(0, ii + 1);
                let tlen: int = t.len() as int;
                assert(tlen == ii + 1);
                assert(count_even(t) == (if t[tlen - 1] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(t.subrange(0, tlen - 1)));
                assert(t[tlen - 1] == s[ii]);
                assert(t.subrange(0, tlen - 1) == s.subrange(0, ii));
                assert(count_even(s.subrange(0, ii + 1)) == (if s[ii] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(s.subrange(0, ii)));
                lemma_vec_map_index(v, ii);
                assert(s@[ii] == (v@)[ii] as int);
                assert((x as int) == s@[ii]);
                assert(old_acc as int == count_even(s.subrange(0, ii)));
                assert(count_even(s.subrange(0, ii + 1)) == count_even(s.subrange(0, ii)));
            }
            acc = old_acc;
        }

        i = i + 1;
    }

    acc
}
// </vc-code>

fn main() {
}

}