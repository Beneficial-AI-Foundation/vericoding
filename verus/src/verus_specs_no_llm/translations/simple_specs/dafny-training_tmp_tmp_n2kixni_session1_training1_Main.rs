// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall |j: int, k: int|0 <= j < k < a.len() ==> a.index(j) <= a.index(k)
}

spec fn spec_find(a: Seq<int>, key: int) -> index: int)
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
method isPalindrome(a: seq<char>) returns (b: bool
    requires
        true
    ensures
        true,
        clauses that specify the palidrome properties
 * 3. verify algorithm. 
 *
 * Notes: a.index(k) accesses element k of a for 0 <= k < a.len()
 * a.index(i..j) is (a seq) with the first j elements minus the first i
 * a.index(0..a.len()) is same as a. 
 */


//ATOM
method isPalindrome(a: seq<char>) returns (b: bool)
;

proof fn lemma_find(a: Seq<int>, key: int) -> (index: int)
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
 * Notes: a.index(k) accesses element k of a for 0 <= k < a.len()
 * a.index(i..j) is (a seq) with the first j elements minus the first i
 * a.index(0..a.len()) is same as a. 
 */


//ATOM
method isPalindrome(a: seq<char>) returns (b: bool)
{
    0
}

}