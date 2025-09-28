// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate num_distinct of prepended sequence to tail */
proof fn num_distinct_prepend(head: int, tail: Seq<int>)
    ensures
        num_distinct(seq![head] + tail) == if tail.contains(head) { num_distinct(tail) } else { 1 + num_distinct(tail) },
    decreases tail.len()
{
    proof {
        let prefix = seq![head] + tail;
        assert(prefix.len() == 1 + tail.len());
        assert(prefix.subrange(1, prefix.len() as int) == tail);
        assert(prefix[0] == head);
        assert(num_distinct(prefix) == if prefix.subrange(1, prefix.len() as int).contains(prefix[0]) { num_distinct(prefix.subrange(1, prefix.len() as int)) } else { 1 + num_distinct(prefix.subrange(1, prefix.len() as int)) });
        assert(num_distinct(prefix) == if tail.contains(head) { num_distinct(tail) } else { 1 + num_distinct(tail) });
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed Vec indexing and maintained loop invariants by snapshotting spec views */
    let n: usize = diameters.len();
    let mut seen: Vec<i8> = Vec::new();
    let mut i: usize = 0usize; // number processed from the right
    let mut cnt: i8 = 0i8;

    while i < n
        invariant
            cnt as int == num_distinct(diameters@.subrange(n as int - i as int, n as int).map(|j, x| x as int)),
            (seen@).map(|k, y| y as int) == diameters@.subrange(n as int - i as int, n as int).map(|j, x| x as int),
        decreases n - i
    {
        let idx = n - 1 - i;
        let d: i8 = diameters[idx];

        // search seen for d
        let mut j: usize = 0usize;
        let mut is_new: bool = true;
        while j < seen.len()
            invariant
                j <= seen.len(),
            decreases seen.len() - j
        {
            if seen[j] == d {
                is_new = false;
                break;
            }
            j += 1;
        }

        // snapshot spec-level views before mutating runtime state
        let tail_spec = diameters@.subrange(n as int - i as int, n as int).map(|j, x| x as int);
        let old_seen_spec = (seen@).map(|k, y| y as int);
        assert(old_seen_spec == tail_spec);

        if is_new {
            // insert at front so seen@ represents seq![d] + old_seen@
            seen.insert(0, d);
            cnt += 1;
        }

        // proof that the invariants are maintained for i+1
        proof {
            let head_spec: int = diameters@[(n as int - 1 - i as int)] as int;

            if is_new {
                // seen did not previously contain d, so tail_spec does not contain head_spec
                assert(!tail_spec.contains(head_spec));
                // after insertion seen@ becomes seq![head_spec] + tail_spec
                assert((seen@).map(|k, y| y as int) == seq![head_spec] + tail_spec);
                // by lemma, num_distinct(seq![head] + tail) == 1 + num_distinct(tail)
                assert(num_distinct(seq![head_spec] + tail_spec) == 1 + num_distinct(tail_spec));
                // cnt was incremented to reflect the new distinct count
                assert((cnt as int) == num_distinct(seq![head_spec] + tail_spec));
            } else {
                // seen previously contained d, so tail_spec contains head_spec
                assert(tail_spec.contains(head_spec));
                // seen@ unchanged and equals tail_spec
                assert((seen@).map(|k, y| y as int) == tail_spec);
                // by lemma, num_distinct(seq![head] + tail) == num_distinct(tail)
                assert(num_distinct(seq![head_spec] + tail_spec) == num_distinct(tail_spec));
                // cnt unchanged and equals new num_distinct
                assert((cnt as int) == num_distinct(seq![head_spec] + tail_spec));
            }
        }

        i += 1;
    }

    // after loop, cnt corresponds to entire sequence
    proof {
        assert(cnt as int == num_distinct(diameters@.subrange(0, n as int).map(|j, x| x as int)));
    }

    cnt
}

// </vc-code>


}

fn main() {}