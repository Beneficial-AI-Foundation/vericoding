// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn concat_strings(strings: Seq<Seq<char>>, index: nat) -> Seq<char>
    decreases strings.len() - index
{
    if index >= strings.len() {
        Seq::<char>::empty()
    } else {
        strings[index as int] + concat_strings(strings, index + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define recursive concat of the first `end` sequences */
spec fn concat_prefix(strings: Seq<Seq<char>>, end: nat) -> Seq<char>
    requires
        end <= strings.len(),
    decreases end
{
    if end == 0 {
        Seq::<char>::empty()
    } else {
        let k: nat = end - 1;
        concat_prefix(strings, k) + strings[k as int]
    }
}

/* helper modified by LLM (iteration 5): relate prefix of length i+1 to length i */
proof fn lemma_concat_prefix_step(strings: Seq<Seq<char>>, i: nat)
    requires
        i < strings.len(),
    ensures
        concat_prefix(strings, i + 1) == concat_prefix(strings, i) + strings[i as int],
{
    let k: nat = i; // since (i + 1) - 1 == i
    assert(concat_prefix(strings, i + 1) == concat_prefix(strings, k) + strings[k as int]);
}

/* helper modified by LLM (iteration 5): relate concat_prefix(k) and concat_strings(k) by induction */
proof fn lemma_concat_prefix_concat_strings(strings: Seq<Seq<char>>, k: nat)
    requires
        k <= strings.len(),
    ensures
        concat_prefix(strings, k) + concat_strings(strings, k) == concat_strings(strings, 0),
    decreases k
{
    if k == 0 {
        assert(concat_prefix(strings, 0) == Seq::<char>::empty());
        // Hence empty + concat_strings(strings,0) == concat_strings(strings,0)
    } else {
        let km1: nat = k - 1;
        assert(km1 < strings.len());
        lemma_concat_prefix_concat_strings(strings, km1);
        lemma_concat_prefix_step(strings, km1);
        assert(concat_strings(strings, km1) == strings[km1 as int] + concat_strings(strings, km1 + 1));
        assert(km1 + 1 == k);
        // From lemma for km1 and the step, the goal follows by associativity
    }
}

/* helper modified by LLM (iteration 5): take-succ property for sequences */
proof fn lemma_take_succ<T>(s: Seq<T>, j: int)
    requires
        0 <= j,
        j < s.len(),
    ensures
        s.take(j + 1) == s.take(j).push(s[j]),
{
    assert(s.take(j + 1) == s.take(j).push(s[j]));
}

/* helper modified by LLM (iteration 5): taking exactly the length yields the original sequence */
proof fn lemma_take_len_is_self<T>(s: Seq<T>)
    ensures
        s.take(s.len()) == s,
{
    assert(s.take(s.len()) == s);
}

/* helper modified by LLM (iteration 5): for any vector-of-vectors, indexing then taking spec equals mapping spec then indexing */
proof fn lemma_vec_index_spec_equals_mapped(strings: Vec<Vec<char>>, i: usize)
    requires
        i < strings.len(),
    ensures
        strings[i]@ == strings@.map(|k, s: Vec<char>| s@)[i as int],
{
    assert(strings@[i as int] == strings[i]@);
}

// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement concatenation with nested loops; fix cast-comparison parsing issue */
    let ghost ss: Seq<Seq<char>> = strings@.map(|i, s: Vec<char>| s@);

    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < strings.len()
        invariant
            i <= strings.len(),
            res@ == concat_prefix(ss, i as nat),
        decreases strings@.len() - (i as nat)
    {
        let inner_len: usize = strings[i].len();
        let mut j: usize = 0;

        while j < inner_len
            invariant
                i < strings.len(),
                j <= inner_len,
                res@ == concat_prefix(ss, i as nat) + (strings[i]@).take(j as int),
            decreases (inner_len as nat) - (j as nat)
        {
            let c = strings[i][j];
            res.push(c);
            proof {
                assert(c == (strings[i]@)[j as int]);
                let ghost s_i: Seq<char> = strings[i]@;
                assert(s_i.len() == strings[i].len() as int);
                assert(j < inner_len);
                assert((j as int) < s_i.len());
                lemma_take_succ::<char>(s_i, j as int);
            }
            j = j + 1;
        }

        proof {
            let ghost s_i: Seq<char> = strings[i]@;
            lemma_take_len_is_self::<char>(s_i);
            assert(ss == strings@.map(|k, s: Vec<char>| s@));
            assert(strings@[i as int] == strings[i]@);
            assert(ss.len() == strings@.len());
            assert(strings@.len() == strings.len() as int);
            assert(i as int < ss.len());
            assert(s_i == ss[i as int]);
            lemma_concat_prefix_step(ss, i as nat);
        }

        i = i + 1;
    }

    proof {
        assert(i == strings.len());
        assert(ss.len() == strings@.len());
        assert(strings@.len() == strings.len() as int);
        assert(i as nat == ss.len());
        assert(res@ == concat_prefix(ss, i as nat));
        lemma_concat_prefix_concat_strings(ss, i as nat);
        assert(concat_prefix(ss, i as nat) + concat_strings(ss, i as nat) == concat_strings(ss, 0));
        assert(concat_strings(ss, i as nat) == Seq::<char>::empty());
    }

    res
}
// </vc-code>


}

fn main() {}