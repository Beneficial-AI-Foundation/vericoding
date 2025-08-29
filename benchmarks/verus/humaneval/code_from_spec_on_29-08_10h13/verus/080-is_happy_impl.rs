use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
proof fn three_distinct_equivalence(s: Seq<char>, i: int)
    requires 0 < i && i + 1 < s.len()
    ensures three_distinct_spec(s, i) <==> (s[i - 1] != s[i] && s[i] != s[i + 1])
{
}

proof fn happy_check_lemma(s: Seq<char>, len: usize)
    requires s.len() == len
    requires len >= 3
    ensures happy_spec(s) <==> (forall|i: int| 1 <= i && i + 1 < len ==> 
        (s[i - 1] != s[i] && s[i] != s[i + 1]))
{
    assert forall|i: int| 0 < i && i + 1 < s.len() implies 
        (three_distinct_spec(s, i) <==> (s[i - 1] != s[i] && s[i] != s[i + 1])) by {
        three_distinct_equivalence(s, i);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def is_happy(s: str) -> bool"
docstring: |
You are given a string s.
Your task is to check if the string is happy or not.
A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
test_cases:
- input: "a"
output: False
- input: "aa"
output: False
- input: "abcd"
output: True
- input: "aabb"
output: False
- input: "adb"
output: True
*/
// </vc-description>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let len = s.len();
    
    /* code modified by LLM (iteration 5): fixed syntax error and loop bounds */
    if len < 3 {
        return false;
    }
    
    let mut i: usize = 1;
    
    while i + 1 < len
        invariant
            1 <= i <= len,
            len >= 3,
            s@.len() == len,
            forall|j: int| 1 <= j < i ==> (s@[j - 1] != s@[j] && s@[j] != s@[j + 1]),
    {
        if s[i - 1] == s[i] || s[i] == s[i + 1] {
            return false;
        }
        i += 1;
    }
    
    proof {
        happy_check_lemma(s@, len);
        assert forall|j: int| 1 <= j && j + 1 < len ==> 
            (s@[j - 1] != s@[j] && s@[j] != s@[j + 1]);
    }
    
    true
}
// </vc-code>

}
fn main() {}