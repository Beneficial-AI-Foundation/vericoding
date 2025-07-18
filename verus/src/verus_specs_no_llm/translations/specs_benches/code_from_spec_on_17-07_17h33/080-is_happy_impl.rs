use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    /* code modified by LLM (iteration 1): fixed duplicate condition in specification */
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}

fn three_distinct(s: &Vec<char>, i: usize) -> (is: bool)
    requires
        0 < i && i + 1 < s.len(),
    ensures
        is <==> three_distinct_spec(s@, i as int),
{
    /* code modified by LLM (iteration 2): added missing third condition to match spec */
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}

spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}

#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    ensures
        happy <==> happy_spec(s@),
{
    /* code modified by LLM (iteration 1): fixed function signature and implemented body */
    if s.len() < 3 {
        return false;
    }
    
    let mut idx = 1;
    /* code modified by LLM (iteration 2): fixed loop condition and invariant to prevent overflow and ensure preconditions */
    while idx < s.len() - 1
        invariant
            1 <= idx <= s.len() - 1,
            forall|i: int| 0 < i < idx && i + 1 < s.len() ==> three_distinct_spec(s@, i),
        decreases s.len() - idx
    {
        if !three_distinct(s, idx) {
            return false;
        }
        idx += 1;
    }
    
    true
}

}
fn main() {}