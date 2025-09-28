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
/* helper modified by LLM (iteration 5): spec fn total_chars counts total characters in a sequence of sequences */
spec fn total_chars(strings: Seq<Seq<char>>) -> nat
    decreases strings.len()
{
    if strings.len() == 0 { 0 } else { strings[0].len() + total_chars(strings.slice(1, strings.len())) }
}

/* helper modified by LLM (iteration 5): spec fn flatten_prefix returns first p chars of flattened strings */
spec fn flatten_prefix(strings: Seq<Seq<char>>, p: nat) -> Seq<char>
    decreases strings.len(), p
{
    if p == 0 {
        Seq::<char>::empty()
    } else if strings.len() == 0 {
        Seq::<char>::empty()
    } else {
        let first = strings[0];
        if p <= first.len() {
            first.slice(0, p)
        } else {
            first + flatten_prefix(strings.slice(1, strings.len()), p - first.len())
        }
    }
}

/* helper modified by LLM (iteration 5): lemma that flatten_prefix at full length equals concat_strings */
proof fn flatten_prefix_full(strings: Seq<Seq<char>>)
    ensures flatten_prefix(strings, total_chars(strings)) == concat_strings(strings, 0)
    decreases strings.len()
{
    if strings.len() == 0 {
        assert(total_chars(strings) == 0);
        assert(flatten_prefix(strings, 0) == Seq::<char>::empty());
    } else {
        let first = strings[0];
        let rest = strings.slice(1, strings.len());
        assert(total_chars(strings) == first.len() + total_chars(rest));
        if total_chars(strings) <= first.len() {
            assert(total_chars(strings) == first.len());
            assert(flatten_prefix(strings, total_chars(strings)) == first.slice(0, first.len()));
            assert(first.slice(0, first.len()) == first);
            assert(total_chars(rest) == 0);
            assert(flatten_prefix(rest, 0) == Seq::<char>::empty());
            assert(concat_strings(rest, 0) == Seq::<char>::empty());
            assert(concat_strings(strings, 0) == first + concat_strings(rest, 0));
            assert(flatten_prefix(strings, total_chars(strings)) == concat_strings(strings, 0));
        } else {
            flatten_prefix_full(rest);
            assert(flatten_prefix(strings, total_chars(strings)) == first + flatten_prefix(rest, total_chars(strings) - first.len()));
            assert(total_chars(strings) - first.len() == total_chars(rest));
            assert(first + flatten_prefix(rest, total_chars(rest)) == first + concat_strings(rest, 0));
            assert(first + concat_strings(rest, 0) == concat_strings(strings, 0));
        }
    }
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
    /* code modified by LLM (iteration 5): build Vec<char> from strings without ghost variables, using invariants with i and j */
    let mut res: Vec<char> = Vec::new();
    let seqs_spec: Seq<Seq<char>> = strings@.map(|i, s: Vec<char>| s@);
    let mut i: usize = 0;
    while i < strings.len()
        invariant
            res@ == flatten_prefix(seqs_spec, total_chars(seqs_spec.slice(0, i as nat))),
        decreases strings.len() - i
    {
        let s = strings.get(i);
        let mut j: usize = 0;
        while j < s.len()
            invariant
                res@ == flatten_prefix(seqs_spec, total_chars(seqs_spec.slice(0, i as nat)) + (j as nat)),
            decreases s.len() - j
        {
            let ch = s.get(j);
            res.push(ch);
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(res@ == flatten_prefix(seqs_spec, total_chars(seqs_spec)));
        flatten_prefix_full(seqs_spec);
        assert(flatten_prefix(seqs_spec, total_chars(seqs_spec)) == concat_strings(seqs_spec, 0));
        assert(res@ == concat_strings(seqs_spec, 0));
    }
    res
}

// </vc-code>


}

fn main() {}