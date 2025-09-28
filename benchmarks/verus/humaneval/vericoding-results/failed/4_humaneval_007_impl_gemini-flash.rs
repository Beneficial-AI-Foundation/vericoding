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
/* helper modified by LLM (iteration 5): Fix compilation errors by casting n to nat in subrange calls. */
use vstd::seq_lib::lemma_seq_properties;

proof fn lemma_filter_sequence_helper_properties(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len()
    ensures
        filter_sequence_helper(strings, substring, n).len() <= n,
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> strings.subrange(0, n as nat).contains(filter_sequence_helper(strings, substring, n)[i]),
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> contains_substring(filter_sequence_helper(strings, substring, n)[i], substring),
        forall|i: int| 0 <= i < n && contains_substring(strings[i], substring) ==> filter_sequence_helper(strings, substring, n).contains(strings[i]),
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> exists|k: int| 0 <= k < n && #[trigger] filter_sequence_helper(strings, substring, n)[i] =~= strings[k],
        forall|s: Seq<char>| filter_sequence_helper(strings, substring, n).contains(s) <==> (strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring))
    decreases n
{
    if n <= 0 {
        assert(filter_sequence_helper(strings, substring, n) =~= strings.take(0));
    } else {
        lemma_filter_sequence_helper_properties(strings, substring, n-1);
        if contains_substring(strings[n-1], substring) {
            assert(filter_sequence_helper(strings, substring, n) =~= filter_sequence_helper(strings, substring, n-1).push(strings[n-1]));
            let prev_result = filter_sequence_helper(strings, substring, n-1);
            assert(prev_result.len() <= n - 1);
            assert(filter_sequence_helper(strings, substring, n).len() == prev_result.len() + 1);
            assert(filter_sequence_helper(strings, substring, n).len() <= n); // prev_result.len() + 1 <= n-1 + 1 = n

            assert(contains_substring(strings[n-1], substring));

            assert(strings.subrange(0, n as nat).contains(strings[n-1]));
            
            assert forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() implies contains_substring(filter_sequence_helper(strings, substring, n)[i], substring) by {
                if i < prev_result.len() {
                    assert(contains_substring(prev_result[i], substring));
                } else {
                    assert(i == prev_result.len());
                    assert(filter_sequence_helper(strings, substring, n)[i] == strings[n-1]);
                    assert(contains_substring(strings[n-1], substring));
                }
            }
            assert forall|i: int| 0 <= i < n && contains_substring(strings[i], substring) implies filter_sequence_helper(strings, substring, n).contains(strings[i]) by {
                if i < n-1 {
                    assert(filter_sequence_helper(strings, substring, n-1).contains(strings[i]));
                    assert(filter_sequence_helper(strings, substring, n).contains(strings[i]));
                } else if i == n-1 {
                    assert(contains_substring(strings[n-1], substring));
                    assert(filter_sequence_helper(strings, substring, n).contains(strings[n-1]));
                }
            }
            assert forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() implies exists|k: int| 0 <= k < n && #[trigger] filter_sequence_helper(strings, substring, n)[i] =~= strings[k] by {
                if i < prev_result.len() {
                    assert(exists|k_prev: int| 0 <= k_prev < n-1 && #[trigger] prev_result[i] =~= strings[k_prev]);
                    let k_val = choose|k_val: int| 0 <= k_val < n-1 && prev_result[i] =~= strings[k_val];
                    assert(exists|k: int| 0 <= k < n && #[trigger] filter_sequence_helper(strings, substring, n)[i] =~= strings[k]) by { let k = k_val; assert(0<=k<n); assert(filter_sequence_helper(strings, substring, n)[i] =~= strings[k]);} 
                } else { // i == prev_result.len()
                    assert(filter_sequence_helper(strings, substring, n)[i] =~= strings[n-1]);
                    assert(exists|k: int| 0 <= k < n && #[trigger] filter_sequence_helper(strings, substring, n)[i] =~= strings[k]) by { let k = n-1; assert(0<=k<n); assert(filter_sequence_helper(strings, substring, n)[i] =~= strings[k]);} 
                }
            }
            assert forall|s: Seq<char>| filter_sequence_helper(strings, substring, n).contains(s) <==> (strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring)) by {
                if filter_sequence_helper(strings, substring, n).contains(s) {
                    if prev_result.contains(s) {
                        assert(strings.subrange(0, (n-1) as nat).contains(s) && contains_substring(s, substring));
                        assert(strings.subrange(0, n as nat).contains(s));
                    } else {
                        assert(s =~= strings[n-1]);
                        assert(contains_substring(strings[n-1], substring));
                        assert(strings.subrange(0, n as nat).contains(strings[n-1]));
                    }
                } else {
                    if strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring) {
                        if s =~= strings[n-1] {
                            // This case implies strings[n-1] is the element 's' that matches substring
                            // and we are in the 'if contains_substring(strings[n-1], substring)' branch
                            // so 's' should be in the result. This contradicts `!filter_sequence_helper(...).contains(s)`
                        } else {
                            assert(strings.subrange(0, (n-1) as nat).contains(s));
                            assert(filter_sequence_helper(strings, substring, n-1).contains(s));
                        }
                    }
                }
            }

        } else {
            assert(filter_sequence_helper(strings, substring, n) =~= filter_sequence_helper(strings, substring, n-1));
            let prev_result = filter_sequence_helper(strings, substring, n-1);
            assert(prev_result.len() <= n - 1);
            assert(filter_sequence_helper(strings, substring, n).len() <= n);

            assert forall|i: int| 0 <= i < n && contains_substring(strings[i], substring)  implies filter_sequence_helper(strings, substring, n).contains(strings[i]) by {
                if i < n-1 {
                    assert(filter_sequence_helper(strings, substring, n-1).contains(strings[i]));
                } else if i == n-1 {
                    assert(!contains_substring(strings[n-1], substring)); // if contains_substring(strings[n-1], substring) were true, it would be added.
                    assert(!filter_sequence_helper(strings, substring, n).contains(strings[n-1]));
                }
            }
            assert forall|s: Seq<char>| filter_sequence_helper(strings, substring, n).contains(s) <==> (strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring)) by {
                if (filter_sequence_helper(strings, substring, n).contains(s)) {
                    assert(filter_sequence_helper(strings, substring, n-1).contains(s));
                    assert(strings.subrange(0, (n-1) as nat).contains(s) && contains_substring(s, substring));
                    assert(strings.subrange(0, n as nat).contains(s));
                } else {
                    if strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring) {
                        if s =~= strings[n-1] {
                            assert(!contains_substring(strings[n-1], substring)); // This branch assumes includes strings[n-1] if it contains substring
                            // This is the case where strings[n-1] caused the 'if contains_substring(strings[n-1], substring)' to be false
                            // It cannot satisfy (strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring))
                            // and filter_sequence_helper(strings, substring, n).contains(s) being false at the same time
                        } else {
                            assert(strings.subrange(0, (n-1) as nat).contains(s));
                            assert(filter_sequence_helper(strings, substring, n-1).contains(s));
                        }
                    }
                }
            }
        }
    }
}

proof fn lemma_subrange_contains_eq_contains(source: Seq<Seq<char>>, len: nat, elem: Seq<char>)
    requires
        0 <= len <= source.len()
    ensures
        source.subrange(0, len).contains(elem) <==> (source.contains(elem) && (exists|i:int| #![auto] 0 <= i < len && source[i] =~= elem))
{
    if source.subrange(0, len as int).contains(elem) {
        let k_sub = choose|k: int| 0 <= k < len as int && source.subrange(0, len as int)[k] =~= elem;
        assert(source[k_sub] =~= elem);
        assert(source.contains(elem));
        assert(exists|i: int| 0 <= i < len && source[i] =~= elem);
    } else {
        if source.contains(elem) && (exists|i: int| 0 <= i < len && source[i] =~= elem) {
            let k = choose|k: int| 0 <= k < len && source[k] =~= elem;
            assert(source.subrange(0, len as int).contains(source[k]));
            assert(source.subrange(0, len as int).contains(elem));
        }
    }
}

proof fn lemma_filter_sequence_properties(strings: Seq<Seq<char>>, substring: Seq<char>)
    ensures
        filter_sequence(strings, substring).len() <= strings.len(),
        forall|i: int| 0 <= i < filter_sequence(strings, substring).len() ==> strings.contains(filter_sequence(strings, substring)[i]),
        forall|i: int| 0 <= i < filter_sequence(strings, substring).len() ==> contains_substring(filter_sequence(strings, substring)[i], substring),
        forall|i: int| 0 <= i < strings.len() && contains_substring(strings[i], substring) ==> filter_sequence(strings, substring).contains(strings[i]),
        forall|i: int, j: int| 0 <= i < j < filter_sequence(strings, substring).len() ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < strings.len() && #[trigger] filter_sequence(strings, substring)[i] =~= strings[k1] && #[trigger] filter_sequence(strings, substring)[j] =~= strings[k2],
        forall|s: Seq<char>| filter_sequence(strings, substring).contains(s) <==> (strings.contains(s) && contains_substring(s, substring))
{
    let n = strings.len();
    lemma_filter_sequence_helper_properties(strings, substring, n as int);

    let result_helper = filter_sequence_helper(strings, substring, n as int);
    let result = filter_sequence(strings, substring);
    assert(result =~= result_helper);

    assert(result.len() <= n);
    assert forall|i: int| 0 <= i < result.len() implies strings.contains(result[i]) by {
        assert(exists|k: int| 0 <= k < n && #[trigger] result[i] =~= strings[k]);
        let k_val = choose|k_val: int| 0 <= k_val < n && result[i] =~= strings[k_val];
        assert(strings.contains(result[i]));
    }
    assert forall|i: int| 0 <= i < result.len() implies contains_substring(result[i], substring) by {
        assert(contains_substring(result_helper[i], substring));
    }
    assert forall|i: int| 0 <= i < strings.len() && contains_substring(strings[i], substring) implies result.contains(strings[i]) by {
        assert(result_helper.contains(strings[i]));
    }
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies
            exists|k1: int, k2: int| 0 <= k1 < k2 < strings.len() && #[trigger] result[i] =~= strings[k1] && #[trigger] result[j] =~= strings[k2] by
    {
        let k1_val = choose|k_val: int| 0 <= k_val < n && result[i] =~= strings[k_val];
        let k2_val = choose|k_val: int| 0 <= k_val < n && result[j] =~= strings[k_val];
        assert(k1_val < k2_val);
    }
    
    assert forall|s: Seq<char>| result.contains(s) <==> (strings.contains(s) && contains_substring(s, substring)) by {
        assert(result_helper.contains(s) <==> (strings.subrange(0, n as nat).contains(s) && contains_substring(s, substring)));
        
        lemma_subrange_contains_eq_contains(strings, n as nat, s);

        if result.contains(s) {
            assert(strings.contains(s) && contains_substring(s, substring));
        } else {
            if strings.contains(s) && contains_substring(s, substring) {
                assert(result_helper.contains(s));
            }
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
/* code modified by LLM (iteration 5): Removed verification bypasses */
{
    lemma_filter_sequence_properties(strings, substring);
    filter_sequence(strings, substring)
}
// </vc-code>


}

fn main() {}