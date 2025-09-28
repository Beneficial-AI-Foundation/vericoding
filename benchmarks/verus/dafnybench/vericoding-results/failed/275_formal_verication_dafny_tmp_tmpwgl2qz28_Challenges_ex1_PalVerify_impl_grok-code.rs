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
fn test_pal_verify() {
    let refer = vec!['r', 'e', 'f', 'e', 'r'];
    assert(pal_verify(&refer));
    let z = vec!['z'];
    assert(pal_verify(&z));
    let empty: Vec<char> = vec![];
    assert(pal_verify(&empty));
    let xy = vec!['x', 'y'];
    assert(!pal_verify(&xy));
    let num = vec!['1', '2', '3', '4', '2', '1'];
    assert(!pal_verify(&num));
}
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let alen: usize = a.len();
    let mut i: usize = 0;
    while i < alen / 2
        invariant
            0 <= i <= alen / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == #[trigger] a@[alen as int - j - 1]
    {
        let idx1 = i;
        let idx2 = alen - i - 1;
        if a[idx1] != a[idx2] {
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