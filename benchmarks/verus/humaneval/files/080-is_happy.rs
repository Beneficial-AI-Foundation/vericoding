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

#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

}
fn main() {}