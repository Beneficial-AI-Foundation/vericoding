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

spec fn sorted(a: Seq<int>) -> bool {
    forall j, k::0 <= j < k < a.len() ==> a.spec_index(j) <= a.spec_index(k)
}

fn find(a: Seq<int>, key: int) -> (index: int)
  requires true
  ensures true
{
  index := 0;
  assume true;
  return index;
}

// Prove more complicated invariants with quantifiers.

/**
 * Palindrome checker.
 * Example 3.
 *
 * Check whether a sequence of letters is a palindrome.
 *
 * Try to:
 * 1. write the algorithm to determine whether a string is a palindrome
 * 2. write the ensures clauses that specify the palidrome properties
 * 3. verify algorithm. 
 *
 * Notes: a[k] accesses element k of a for 0 <= k < |a|
 * a[i..j] is (a seq) with the first j elements minus the first i
 * a[0..|a|] is same as a. 
 */


//ATOM
method isPalindrome(a: seq<char>) returns (b: bool)
    requires
        true
    ensures
        true,
        clauses that specify the palidrome properties
 * 3. verify algorithm. 
 *
 * Notes: a.spec_index(k) accesses element k of a for 0 <= k < a.len()
 * a.spec_index(i..j) is (a seq) with the first j elements minus the first i
 * a.spec_index(0..a.len()) is same as a. 
 */


//ATOM
method isPalindrome(a: seq<char>) returns (b: bool)
{
    return 0;
}

}