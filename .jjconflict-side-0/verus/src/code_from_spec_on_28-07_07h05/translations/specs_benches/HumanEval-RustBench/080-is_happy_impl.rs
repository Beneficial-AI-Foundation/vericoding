use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end

fn three_distinct(s: &Vec<char>, i: usize) -> (is: bool)
    // pre-conditions-start
    requires
        0 < i && i + 1 < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        is <==> three_distinct_spec(s@, i as int),
    // post-conditions-end
{
    s[i - 1] != s[i] && s[i] != s[i + 1] && s[i] != s[i + 1]
}

spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
{
    if s.len() < 3 {
        return false;
    }
    
    let mut j = 1;
    /* code modified by LLM (iteration 1): changed loop condition to avoid overflow and ensure precondition */
    while j < s.len() - 1
        invariant
            1 <= j <= s.len(),
            forall|i: int| 0 < i < j && i + 1 < s.len() ==> three_distinct_spec(s@, i),
        decreases s.len() - j,
    {
        /* code modified by LLM (iteration 1): precondition is now satisfied since j >= 1 and j < s.len() - 1 implies j + 1 < s.len() */
        if !three_distinct(s, j) {
            return false;
        }
        j += 1;
    }
    
    true
}

}
fn main() {}