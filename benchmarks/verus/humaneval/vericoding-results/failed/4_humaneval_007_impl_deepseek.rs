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
proof fn lemma_filter_sequence_helper_contains(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len(),
    ensures
        forall|s: Seq<char>| filter_sequence_helper(strings, substring, n).contains(s) <==> 
            (exists|i: int| 0 <= i < n && strings[i] =~= s && contains_substring(s, substring)),
    decreases n
{
    if n > 0 {
        lemma_filter_sequence_helper_contains(strings, substring, n - 1);
        let prev = filter_sequence_helper(strings, substring, n - 1);
        let current = strings[n - 1];
        if contains_substring(current, substring) {
            assert forall|s: Seq<char>| prev.push(current).contains(s) <==> (prev.contains(s) || s =~= current) by {
                assert(prev.push(current).contains(s) == (prev.contains(s) || s =~= current));
            };
        } else {
            assert(filter_sequence_helper(strings, substring, n) == prev);
        }
    }
}

proof fn lemma_filter_sequence_helper_len(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len(),
    ensures
        filter_sequence_helper(strings, substring, n).len() <= n,
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> 
            exists|j: int| 0 <= j < n && strings[j] =~= filter_sequence_helper(strings, substring, n)[i],
    decreases n
{
    if n > 0 {
        lemma_filter_sequence_helper_len(strings, substring, n - 1);
        let prev = filter_sequence_helper(strings, substring, n - 1);
        let current = strings[n - 1];
        if contains_substring(current, substring) {
            assert(prev.push(current).len() == prev.len() + 1);
            assert(prev.len() <= n - 1);
            assert(prev.push(current).len() <= n);
        }
    }
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
    /* code modified by LLM (iteration 5): Fix type errors and indexing issues */
    let mut result: Seq<Seq<char>> = Seq::empty();
    let mut i: int = 0;
    
    while i < strings.len() as int
        invariant
            i >= 0,
            i <= strings.len() as int,
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> contains_substring(result[j], substring),
            forall|j: int| 0 <= j < i && contains_substring(strings[j as nat], substring) ==> result.contains(strings[j as nat]),
            forall|s: Seq<char>| result.contains(s) <==> (exists|j: int| 0 <= j < i && strings[j as nat] =~= s && contains_substring(s, substring)),
            result =~= filter_sequence_helper(strings, substring, i),
        decreases strings.len() as int - i
    {
        if contains_substring(strings[i as nat], substring) {
            result = result.push(strings[i as nat]);
        }
        i = i + 1;
    }
    
    proof {
        lemma_filter_sequence_helper_contains(strings, substring, strings.len() as int);
        lemma_filter_sequence_helper_len(strings, substring, strings.len() as int);
        assert(filter_sequence(strings, substring) =~= filter_sequence_helper(strings, substring, strings.len() as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}