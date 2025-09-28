use vstd::prelude::*;

verus! {

// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome
/*
A Palindrome is a word that is the same when written forwards and when written backwards. 
For example, the word "refer" is a Palindrome.
The method PalVerify is supposed to verify whether a word is a Palindrome, 
where the word is represented as an array of characters. 
The method was written by a novice software engineer, and contains many errors.

   i) Without changing the signature or the code in the while loop, 
      fix the method so that it veriifes the code. Do not add any Dafny predicates or functions: 
      keep the changes to a minimum.

   ii) Write a tester method (you may call it anything you like) that verifies that the 
      testcases refer, z and the empty string are Palindromes, and xy and 123421 are not. 
      The tester should not generate any output.
*/

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut j: int = a.len() as int - 1;

    while i < j
        invariant
            0 <= i,
            0 <= j,
            i <= j + 1, // i and j are moving towards each other, i never crosses j in a way that i > j+1
            j < a.len() as int,
            i + j == a.len() as int - 1,
            forall|k: int| 0 <= k < i ==> #[trigger] a[k] == #[trigger] a[a.len() - k - 1],
    {
        if a[i] != a[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }

    proof {
        // When the loop terminates, i >= j.
        // Combined with the invariant i <= j + 1, we have i = j or i = j+1.
        // Also from invariant: i + j == a.len() - 1.

        // Case 1: i = j.
        // Then i + i = a.len() - 1 => 2*i = a.len() - 1.
        // This implies a.len() is odd. i = (a.len() - 1) / 2.
        // Since `a.len() / 2` (integer division) for odd `a.len()` is also `(a.len() - 1) / 2`,
        // we have i = a.len() / 2.

        // Case 2: i = j + 1.
        // Then (j + 1) + j = a.len() - 1 => 2*j + 1 = a.len() - 1 => 2*j = a.len() - 2 => j = (a.len() - 2) / 2.
        // And i = j + 1 = (a.len() - 2) / 2 + 1 = a.len() / 2 - 1 + 1 = a.len() / 2.
        // This implies a.len() is even. i = a.len() / 2.

        // In both cases, at termination, i == a.len() / 2.
        // The invariant `forall|k: int| 0 <= k < i ==> a[k] == a[a.len() - k - 1]`
        // becomes `forall|k: int| 0 <= k < a.len() / 2 ==> a[k] == a[a.len() - k - 1]`.
        assert(i == a.len() as int / 2);
    }
    true
}
// </vc-code>

fn main() {
}

}