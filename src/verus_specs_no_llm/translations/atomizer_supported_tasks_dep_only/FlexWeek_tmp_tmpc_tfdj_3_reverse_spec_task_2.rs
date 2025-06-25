// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

// SPEC 
// Write an *iterative* Dafny method Reverse with signature: //          method Reverse(a: array<char>) returns (b: array<char>)

// which takes an input array of characters 'a' and outputs array 'b' consisting of
// the elements of the input array in reverse order. The following conditions apply:
//  - the input array cannot be empty
//  - the input array is not modified
//  - you must use iteration
//  - not permitted is an *executable* (parallel) forall statement
//  - not permitted are any other predicates, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

method Reverse(a: Vec<char>) returns (b: array<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall k :: 0 <= k < a.len() ==> b.spec_index(k) == a.spec_index((a.len()-1) - k);
{
    return Vec::new();
}

}