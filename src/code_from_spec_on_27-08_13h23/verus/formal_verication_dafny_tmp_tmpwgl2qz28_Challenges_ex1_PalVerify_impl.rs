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
proof fn test_pal_verify()
    ensures
        // Test cases for palindromes: "refer", "z", and empty string
        pal_verify(&vec!['r', 'e', 'f', 'e', 'r']) == true,
        pal_verify(&vec!['z']) == true,
        pal_verify(&vec![]) == true,
        // Test cases for non-palindromes: "xy" and "123421"
        pal_verify(&vec!['x', 'y']) == false,
        pal_verify(&vec!['1', '2', '3', '4', '2', '1']) == false,
{
    assert(pal_verify(&vec!['r', 'e', 'f', 'e', 'r']) == true);
    assert(pal_verify(&vec!['z']) == true);
    assert(pal_verify(&vec![]) == true);
    assert(pal_verify(&vec!['x', 'y']) == false);
    assert(pal_verify(&vec!['1', '2', '3', '4', '2', '1']) == false);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let len = a.len();
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] == #[trigger] a[len - j - 1],
    {
        if a[i] != a[len - i - 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}