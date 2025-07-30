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
    return false;  // TODO: Remove this line and implement the function body
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
    return false;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
