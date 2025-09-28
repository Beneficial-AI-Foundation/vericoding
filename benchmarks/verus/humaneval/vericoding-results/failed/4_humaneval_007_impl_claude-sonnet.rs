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
/* helper modified by LLM (iteration 5): Fixed type conversions and sequence comparison issues */
exec fn filter_sequence_exec(strings: Seq<Seq<char>>, substring: Seq<char>) -> (result: Seq<Seq<char>>)
    ensures
        result =~= filter_sequence(strings, substring)
{
    filter_sequence_helper_exec(strings, substring, strings.len() as usize)
}

exec fn filter_sequence_helper_exec(strings: Seq<Seq<char>>, substring: Seq<char>, n: usize) -> (result: Seq<Seq<char>>)
    requires
        n <= strings.len()
    ensures
        result =~= filter_sequence_helper(strings, substring, n as int)
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else if contains_substring_exec(strings[n-1], substring) {
        filter_sequence_helper_exec(strings, substring, n-1).push(strings[n-1])
    } else {
        filter_sequence_helper_exec(strings, substring, n-1)
    }
}

exec fn contains_substring_exec(s: Seq<char>, sub: Seq<char>) -> (result: bool)
    ensures
        result == contains_substring(s, sub)
    decreases s.len()
{
    if sub.len() == 0nat {
        true
    } else if sub.len() > s.len() {
        false
    } else if s.len() == sub.len() {
        s =~= sub
    } else {
        (s.subrange(0int, sub.len() as int) =~= sub) || contains_substring_exec(s.subrange(1int, s.len() as int), sub)
    }
}

proof fn filter_sequence_helper_properties(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len()
    ensures
        filter_sequence_helper(strings, substring, n).len() <= n,
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> strings.contains(filter_sequence_helper(strings, substring, n)[i]),
        forall|i: int| 0 <= i < filter_sequence_helper(strings, substring, n).len() ==> contains_substring(filter_sequence_helper(strings, substring, n)[i], substring),
        forall|i: int| 0 <= i < n && contains_substring(strings[i], substring) ==> filter_sequence_helper(strings, substring, n).contains(strings[i]),
        forall|s: Seq<char>| filter_sequence_helper(strings, substring, n).contains(s) <==> (exists|j: int| 0 <= j < n && strings[j] =~= s && contains_substring(s, substring))
    decreases n
{
    if n <= 0 {
    } else if contains_substring(strings[n-1], substring) {
        filter_sequence_helper_properties(strings, substring, n-1);
    } else {
        filter_sequence_helper_properties(strings, substring, n-1);
    }
}

proof fn filter_sequence_order_preserved(strings: Seq<Seq<char>>, substring: Seq<char>)
    ensures
        forall|i: int, j: int| 0 <= i < j < filter_sequence(strings, substring).len() ==>
            exists|k1: int, k2: int| 0 <= k1 < k2 < strings.len() && filter_sequence(strings, substring)[i] =~= strings[k1] && filter_sequence(strings, substring)[j] =~= strings[k2]
{
    filter_sequence_helper_order_preserved(strings, substring, strings.len() as int);
}

proof fn filter_sequence_helper_order_preserved(strings: Seq<Seq<char>>, substring: Seq<char>, n: int)
    requires
        0 <= n <= strings.len()
    ensures
        forall|i: int, j: int| 0 <= i < j < filter_sequence_helper(strings, substring, n).len() ==>
            exists|k1: int, k2: int| 0 <= k1 < k2 < n && filter_sequence_helper(strings, substring, n)[i] =~= strings[k1] && filter_sequence_helper(strings, substring, n)[j] =~= strings[k2]
    decreases n
{
    if n <= 0 {
    } else {
        filter_sequence_helper_order_preserved(strings, substring, n-1);
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
    /* code modified by LLM (iteration 5): Fixed implementation with proper proof calls */
    proof {
        let ghost_len = strings.len() as int;
        filter_sequence_helper_properties(strings, substring, ghost_len);
        filter_sequence_order_preserved(strings, substring);
    }
    filter_sequence_exec(strings, substring)
}
// </vc-code>


}

fn main() {}