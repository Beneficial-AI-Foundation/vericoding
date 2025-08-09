use vstd::prelude::*;

verus! {
    spec fn count_occurrences<T>(s: Seq<T>, key: T) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0nat
        } else {
            let first_match: nat = if s[0] === key { 1nat } else { 0nat };
            first_match + count_occurrences(s.subrange(1, s.len() as int), key)
        }
    }

    fn only_once(a: &[i32], key: i32) -> (b: bool)
        ensures (count_occurrences(a@, key) == 1) <==> b
    {
    return false;  // TODO: Remove this line and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}