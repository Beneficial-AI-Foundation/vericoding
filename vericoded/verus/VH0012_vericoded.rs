// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_result(strings: Seq<Seq<char>>, result: Option<Seq<char>>) -> bool {
    if strings.len() == 0 {
        matches!(result, Option::None)
    } else {
        match result {
            Option::Some(value) => {
                exists|i: int| 0 <= i < strings.len() && #[trigger] strings[i] == value &&
                (forall|s: Seq<char>| strings.contains(s) ==> value.len() >= #[trigger] (s.len())) &&
                (forall|j: int| 0 <= j < i ==> #[trigger] (strings[j].len()) < value.len())
            },
            Option::None => false
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): arithmetic cast monotonicity for usize */
proof fn lemma_usize_cast_preserves_lt(u: usize, v: usize)
    requires
        u < v,
    ensures
        (u as int) < (v as int),
{}

/* helper modified by LLM (iteration 2): bound of usize index as int within a given length */
proof fn lemma_usize_index_in_bounds(u: usize, len: usize)
    requires
        u < len,
    ensures
        0 <= (u as int),
        (u as int) < (len as int),
{}
// </vc-helpers>

// <vc-spec>
fn longest(strings: Vec<Vec<char>>) -> (result: Option<Vec<char>>)
    ensures match result {
        Option::Some(value) => valid_result(strings@.map(|_i: int, v: Vec<char>| v@), Option::Some(value@)),
        Option::None => valid_result(strings@.map(|_i: int, v: Vec<char>| v@), Option::None),
    }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix invariant parsing and proof structure */
    if strings.len() == 0 {
        return Option::None;
    }

    let mut i: usize = 1;
    let mut best: usize = 0;

    while i < strings.len()
        invariant
            1 <= (i as int),
            (i as int) <= (strings.len() as int),
            0 <= (best as int),
            (best as int) <= (i as int) - 1,
            forall|j: int| 0 <= j && j < (i as int) ==> strings@[j]@.len() <= strings@[(best as int)]@.len(),
            forall|j: int| 0 <= j && j < (best as int) ==> strings@[j]@.len() < strings@[(best as int)]@.len(),
        decreases (strings.len() as int) - (i as int)
    {
        let curr_len = strings[i].len();
        let best_len = strings[best].len();
        assert(strings@[(i as int)]@.len() == curr_len as int);
        assert(strings@[(best as int)]@.len() == best_len as int);
        if curr_len > best_len {
            best = i;
        }
        i = i + 1;
    }

    let value = strings[best].clone();

    proof {
        let strings_seq: Seq<Seq<char>> = strings@.map(|_k: int, v: Vec<char>| v@);
        assert(strings_seq.len() == strings.len() as int);
        assert(0 <= (best as int) && (best as int) < strings_seq.len());
        assert(strings_seq[(best as int)] == strings@[(best as int)]@);
        assert(value@ == strings@[(best as int)]@);

        assert(forall|s: Seq<char>| strings_seq.contains(s) ==> value@.len() >= s.len()) by {
            assert forall|s: Seq<char>| strings_seq.contains(s) implies value@.len() >= s.len() by {
                if strings_seq.contains(s) {
                    let k = choose|k: int| 0 <= k && k < strings.len() as int && strings@[k]@ == s;
                    assert(0 <= k && k < strings.len() as int);
                    assert(strings@[k]@ == s);
                    assert(strings@[k]@.len() <= strings@[(best as int)]@.len());
                    assert(value@.len() == strings@[(best as int)]@.len());
                    assert(value@.len() >= s.len());
                }
            }
        }

        assert(forall|j: int| 0 <= j && j < (best as int) ==> strings@[j]@.len() < value@.len()) by {
            assert forall|j: int| 0 <= j && j < (best as int) implies strings@[j]@.len() < value@.len() by {
                if 0 <= j && j < (best as int) {
                    assert(strings@[j]@.len() < strings@[(best as int)]@.len());
                    assert(value@.len() == strings@[(best as int)]@.len());
                }
            }
        }
    }

    Option::Some(value)
}
// </vc-code>


}

fn main() {}