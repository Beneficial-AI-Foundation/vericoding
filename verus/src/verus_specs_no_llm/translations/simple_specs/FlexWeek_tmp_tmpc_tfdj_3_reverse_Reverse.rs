// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Reverse(a: Vec<char>) -> b: array<char>)

// which takes an input array of characters 'a' and outputs array 'b' consisting of
// the elements of the input array in reverse order. The following conditions apply:
// - the input array cannot be empty
// - the input array is not modified
// - you must use iteration
// - not permitted is an *executable* (parallel) forall statement
// - not permitted are any other predicates, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

method Reverse(a: array<char>) returns (b: array<char>
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall |k: int| 0 <= k < a.len() ==> b.index(k) == a.index((a.len()-1) - k)
;

proof fn lemma_Reverse(a: Vec<char>) -> (b: Vec<char>, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

method Reverse(a: Vec<char>) returns (b: array<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall |k: int| 0 <= k < a.len() ==> b.index(k) == a.index((a.len()-1) - k)
{
    Vec::new()
}

}