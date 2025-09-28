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
proof fn lemma_filter_sequence_helper_properties(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len()
    ensures
        filter_sequence_helper(strings, substring, n).len() <= n,
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> strings.take(n).contains(filter_sequence_helper(strings, substring, n)[i]),
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> contains_substring(filter_sequence_helper(strings, substring, n)[i], substring),
        forall|i: int| 0 <= i < n && contains_substring(strings[i], substring) ==> filter_sequence_helper(strings, substring, n).contains(strings[i])
    decreases n
{
    if n <= 0 {
    } else if contains_substring(strings[n-1], substring) {
        lemma_filter_sequence_helper_properties(strings, substring, n-1);
    } else {
        lemma_filter_sequence_helper_properties(strings, substring, n-1);
    }
}

proof fn lemma_filter_sequence_helper_order(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len()
    ensures
        forall|i: int, j: int| 0 <= i < j < filter_sequence_helper(strings, substring, n).len() ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < n && filter_sequence_helper(strings, substring, n)[i] =~= strings[k1] && filter_sequence_helper(strings, substring, n)[j] =~= strings[k2]
    decreases n
{
    if n <= 0 {
    } else if contains_substring(strings[n-1], substring) {
        lemma_filter_sequence_helper_order(strings, substring, n-1);
        let prev = filter_sequence_helper(strings, substring, n-1);
        let curr = filter_sequence_helper(strings, substring, n);
        assert(curr =~= prev.push(strings[n-1]));
        assert forall|i: int, j: int| 0 <= i < j < curr.len() implies 
            exists|k1: int, k2: int| 0 <= k1 < k2 < n && curr[i] =~= strings[k1] && curr[j] =~= strings[k2] by {
            if j == curr.len() - 1 {
                assert(curr[j] =~= strings[n-1]);
                if i < prev.len() {
                    let k1 = choose|k: int| 0 <= k < n-1 && prev[i] =~= strings[k];
                    assert(0 <= k1 < n-1 < n);
                    assert(curr[i] =~= strings[k1] && curr[j] =~= strings[n-1]);
                }
            } else {
                assert(i < j < prev.len());
            }
        }
    } else {
        lemma_filter_sequence_helper_order(strings, substring, n-1);
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
    /* code modified by LLM (iteration 5): Fixed indexing - use usize directly instead of casting to int */
    let mut result: Vec<Seq<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant
            i <= strings.len(),
            result@.len() <= i,
            result@ =~= filter_sequence_helper(strings, substring, i as int),
            forall|j: int| 0 <= j < result@.len() ==> strings.take(i as int).contains(result@[j]),
            forall|j: int| 0 <= j < result@.len() ==> contains_substring(result@[j], substring),
            forall|j: int| 0 <= j < i && contains_substring(strings[j], substring) ==> result@.contains(strings[j]),
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < i && result@[j] =~= strings[k1] && result@[k] =~= strings[k2]
    {
        let s = strings[i];
        if contains_substring(s, substring) {
            result.push(s);
        }
        
        proof {
            lemma_filter_sequence_helper_properties(strings, substring, (i + 1) as int);
            lemma_filter_sequence_helper_order(strings, substring, (i + 1) as int);
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_filter_sequence_helper_properties(strings, substring, strings.len() as int);
        lemma_filter_sequence_helper_order(strings, substring, strings.len() as int);
        assert(result@ =~= filter_sequence_helper(strings, substring, strings.len() as int));
        assert(result@ =~= filter_sequence(strings, substring));
        
        assert forall|s: Seq<char>| result@.contains(s) implies (strings.contains(s) && contains_substring(s, substring)) by {
            if result@.contains(s) {
                let idx = choose|j: int| 0 <= j < result@.len() && result@[j] =~= s;
                assert(strings.contains(result@[idx]));
                assert(contains_substring(result@[idx], substring));
                assert(strings.contains(s));
                assert(contains_substring(s, substring));
            }
        }
        
        assert forall|s: Seq<char>| (strings.contains(s) && contains_substring(s, substring)) implies result@.contains(s) by {};
    }
    
    result@
}
// </vc-code>


}

fn main() {}