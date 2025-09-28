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
/* helper modified by LLM (iteration 5): fixed type conversions by using usize for lengths and indices */
fn exec_contains_substring(s: Seq<char>, sub: Seq<char>) -> (result: bool)
    ensures result == contains_substring(s, sub)
{
    let n = s.len();
    let m = sub.len();
    if m == 0 {
        true
    } else if m > n {
        false
    } else {
        let mut found = false;
        let mut i = 0;
        while i <= n - m
            invariant
                0 <= i <= n - m,
                found == (exists|j: int| 0 <= j < (i as int) && 
                    (forall|k: int| 0 <= k < (m as int) ==> s@[j+k] == sub@[k]))
            decreases (n - m) - i
        {
            let mut j = 0;
            let mut match_found = true;
            while j < m
                invariant
                    0 <= j <= m,
                    match_found == (forall|k: int| 0 <= k < (j as int) ==> s@[i as int + k] == sub@[k])
                decreases m - j
            {
                if s[i+j] != sub[j] {
                    match_found = false;
                    break;
                }
                j += 1;
            }
            if match_found {
                found = true;
                break;
            }
            i += 1;
        }
        found
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
/* code modified by LLM (iteration 5): fixed type conversions by using usize for indices */
{
    let mut result = Seq::<Seq<char>>::empty();
    let mut i = 0;
    let len = strings.len();
    while i < len
        invariant
            0 <= i <= len,
            result =~= filter_sequence_helper(strings, substring, i as int)
        decreases len - i
    {
        if exec_contains_substring(strings[i], substring) {
            result = result.push(strings[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}