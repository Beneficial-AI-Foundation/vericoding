use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    /* code modified by LLM (iteration 1): fixed bug - changed second (s[i] != s[i + 1]) to (s[i - 1] != s[i + 1]) */
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
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
    let prev = s[i - 1];
    let curr = s[i];
    let next = s[i + 1];
    
    /* code modified by LLM (iteration 1): fixed bug - changed second (curr != next) to (prev != next) */
    (prev != curr) && (curr != next) && (prev != next)
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
    
    let mut i = 1;
    while i + 1 < s.len()
        invariant
            1 <= i <= s.len(),
            forall|j: int| 1 <= j < i ==> three_distinct_spec(s@, j),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases s.len() - i
    {
        if !three_distinct(s, i) {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}