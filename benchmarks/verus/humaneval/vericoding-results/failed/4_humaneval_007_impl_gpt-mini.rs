// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn contains_substring(s: Seq<char>, sub: Seq<char>) -> bool
    decreases s.len()
{
    if sub.len() == 0 { 
        true
    } else if sub.len() > s.len() { 
        false
    } else if s.len() == sub.len() {
        s == sub
    } else {
        (s.subrange(0, sub.len() as int) == sub) || contains_substring(s.subrange(1, s.len() as int), sub)
    }
}

spec fn filter_sequence(strings: Seq<Seq<char>>, substring: Seq<char>) -> Seq<Seq<char>> {
    filter_sequence_helper(strings, substring, strings.len() as int)
}

spec fn filter_sequence_helper(strings: Seq<Seq<char>>, substring: Seq<char>, n: int) -> Seq<Seq<char>>
    decreases n when 0 <= n <= strings.len()
{
    if n <= 0 {
        strings.take(0 as int)
    } else if contains_substring(strings[n-1], substring) {
        filter_sequence_helper(strings, substring, n-1).push(strings[n-1])
    } else {
        filter_sequence_helper(strings, substring, n-1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that filter_sequence_helper with n=0 returns empty sequence */
proof fn lemma_filter_sequence_helper_zero(strings: Seq<Seq<char>>, substring: Seq<char>)
    ensures
        filter_sequence_helper(strings, substring, 0) =~= strings.take(0),
{
    reveal(filter_sequence_helper);
    assert(filter_sequence_helper(strings, substring, 0) =~= strings.take(0));
}

// </vc-helpers>

// <vc-spec>
fn filter_by_substring(strings: Seq<Seq<char>>, substring: Seq<char>) -> (result: Seq<Seq<char>>)
    ensures 
        result.len() <= strings.len(),
        forall|i: int| 0 <= i < result.len() ==> strings.contains(result[i]),
        forall|i: int| 0 <= i < result.len() ==> contains_substring(result[i], substring),
        forall|i: int| 0 <= i < strings.len() && contains_substring(strings[i], substring) ==> result.contains(strings[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < strings.len() && #[trigger] result[i] =~= strings[k1] && #[trigger] result[j] =~= strings[k2],
        forall|s: Seq<char>| result.contains(s) <==> (strings.contains(s) && contains_substring(s, substring)),
        result =~= filter_sequence(strings, substring)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): move ghost loop into proof block to avoid nat/int in runtime */
    let mut res: Seq<Seq<char>> = Seq::empty();

    proof {
        let mut i: int = 0;
        reveal(filter_sequence_helper);
        assert(res =~= filter_sequence_helper(strings, substring, 0));
        while i < strings.len() as int
            invariant
                0 <= i <= strings.len() as int,
                res =~= filter_sequence_helper(strings, substring, i),
            decreases strings.len() as int - i
        {
            if contains_substring(strings@[i], substring) {
                res = res.push(strings@[i]);
            }
            i = i + 1;
        }
    }

    res
}

// </vc-code>


}

fn main() {}