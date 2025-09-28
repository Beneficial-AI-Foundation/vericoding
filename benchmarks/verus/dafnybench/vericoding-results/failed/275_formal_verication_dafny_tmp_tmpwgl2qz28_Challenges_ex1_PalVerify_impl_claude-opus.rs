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
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let mut yn = true;
    let mut i: usize = 0;
    
    while i < a.len() / 2
        invariant
            0 <= i <= a.len() / 2,
        invariant
            yn == (forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == #[trigger] a@[a@.len() as int - j - 1]),
        invariant
            !yn ==> exists|j: int| #![trigger(a@[j], a@[a@.len() as int - j - 1])] 0 <= j < i && a@[j] != a@[a@.len() as int - j - 1],
    {
        if a[i] != a[a.len() - i - 1] {
            yn = false;
        }
        i = i + 1;
    }
    
    yn
}
// </vc-code>

fn main() {
}

}