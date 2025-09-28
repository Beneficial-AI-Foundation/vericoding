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
/* helper modified by LLM (iteration 5): fixed 'result' scope to solve name resolution error and added an exec helper */
proof fn filter_by_substring_recursive(strings: Seq<Seq<char>>, substring: Seq<char>, n: int) -> (result: Seq<Seq<char>>)
    requires
        0 <= n <= strings.len() as int,
    ensures
        result == filter_sequence_helper(strings, substring, n),
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        let prev_result = filter_by_substring_recursive(strings, substring, n - 1);
        if contains_substring(strings[(n - 1) as nat], substring) {
            prev_result.push(strings[(n - 1) as nat])
        } else {
            prev_result
        }
    }
}

fn exec_contains_substring(s: &Vec<char>, sub: &Vec<char>) -> (b: bool)
    ensures b == contains_substring(s@, sub@),
    decreases s.len()
{
    if sub.len() == 0 {
        true
    } else if sub.len() > s.len() {
        false
    } else {
        let s_len = s.len();
        let sub_len = sub.len();

        let mut prefix_match = true;
        let mut i = 0;
        while i < sub_len
            invariant
                0 <= i <= sub_len,
                prefix_match <==> s@.subrange(0, i as int) == sub@.subrange(0, i as int),
            decreases sub_len - i
        {
            if s[i] != sub[i] {
                prefix_match = false;
                break;
            }
            i = i + 1;
        }

        if prefix_match {
            proof {
                assert(s@.subrange(0, sub@.len()) == sub@);
                assert(contains_substring(s@, sub@));
            }
            true
        } else {
            proof {
                assert(s@.subrange(0, sub@.len()) != sub@);
                assert(contains_substring(s@, sub@) <==> contains_substring(s@.subrange(1, s@.len()), sub@));
            }
            let s_slice: Vec<char> = s.subslice(1, s_len);
            assert(s_slice@ == s@.subrange(1, s_len as int));
            exec_contains_substring(&s_slice, sub)
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
/* code modified by LLM (iteration 5): implemented with a while-loop and an exec helper for substring checks */
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            result@ =~= filter_sequence(strings@.take(i as int), substring@),
    {
        let s = strings.index(i);
        if exec_contains_substring(&s, &substring) {
            proof {
                let strings_i = strings@.take(i as int);
                let s_seq = s@;
                assert(filter_sequence(strings_i.push(s_seq), substring@) 
                    == filter_sequence(strings_i, substring@).push(s_seq));
            }
            result.push(s);
        } else {
            proof {
                let strings_i = strings@.take(i as int);
                let s_seq = s@;
                assert(filter_sequence(strings_i.push(s_seq), substring@) 
                    == filter_sequence(strings_i, substring@));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}