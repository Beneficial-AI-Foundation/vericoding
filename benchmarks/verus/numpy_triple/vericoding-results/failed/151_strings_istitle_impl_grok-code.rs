// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
spec fn is_upper(c: char) -> bool { 'A' <= c && c <= 'Z' }

spec fn is_lower(c: char) -> bool { 'a' <= c && c <= 'z' }

spec fn is_titlecased(s: Seq<char>) -> bool {
    if s.len() == 0 {
        true
    } else {
        is_upper(s[0]) &&
        forall|i: int| 1 <= i < s.len() ==> is_lower(s[i])
    }
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == is_titlecased(a[j]@)
    {
        result.push(is_titlecased(a[i]@));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}