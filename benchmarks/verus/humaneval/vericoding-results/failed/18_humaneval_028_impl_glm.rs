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
spec fn prefix_concat(strings: SeqSeq<char>>, i: nat) -> Seq<char>
    decreases i
{
    if i == 0 {
        Seq::<char>::empty()
    } else {
        prefix_concat(strings, (i-1) as nat) + strings[i-1]
    }
}

/* helper modified by LLM (iteration 5): fixed termination by changing decreases clause to i */
proof fn lemma_concat_split(strings: SeqSeq<char>>, i: nat)
    requires i <= strings.len()
    ensures prefix_concat(strings, i) + concat_strings(strings, i) == concat_strings(strings, 0)
    decreases i
{
    if i == 0 {
        assert(prefix_concat(strings,0) == Seq::<char>::empty());
        assert(concat_strings(strings,0) == concat_strings(strings,0));
    } else {
        lemma_concat_split(strings, (i-1) as nat);
        let pre = prefix_concat(strings, (i-1) as nat);
        let s = strings[i-1];
        let post = concat_strings(strings, i);
        assert(pre + (s + post) == concat_strings(strings,0));
        assert(prefix_concat(strings, i) == pre + s);
        assert((pre + s) + post == pre + (s + post));
        assert(prefix_concat(strings, i) + post == concat_strings(strings,0));
    }
}

/* helper modified by LLM (iteration 2): removed nested function and updated to call top-level lemma */
proof fn lemma_prefix_concat_eq_concat(strings: SeqSeq<char>>)
    ensures prefix_concat(strings, strings.len()) == concat_strings(strings, 0)
{
    let n = strings.len();
    if n == 0 {
        assert(prefix_concat(strings, 0) == Seq::<char>::empty());
        assert(concat_strings(strings,0) == Seq::<char>::empty());
    } else {
        lemma_concat_split(strings, n);
        assert(concat_strings(strings, n) == Seq::<char>::empty());
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
    /* code modified by LLM (iteration 5): updated comment only, no code changes */
    let mut result = Vec::<char>::new();
    let mut i = 0;
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            result@ == prefix_concat(strings@.map(|j, s: Vec<char>| s@), i as nat)
        decreases strings.len() - i
    {
        let s = &strings[i];
        let mut j = 0;
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                result@ == prefix_concat(strings@.map(|k, t: Vec<char>| t@), i as nat) + s@.subrange(0, j as int)
            decreases s.len() - j
        {
            result.push(s[j]);
            j += 1;
        }
        i += 1;
    }
    proof {
        lemma_prefix_concat_eq_concat(strings@.map(|j, s: Vec<char>| s@));
    }
    result
}
// </vc-code>


}

fn main() {}