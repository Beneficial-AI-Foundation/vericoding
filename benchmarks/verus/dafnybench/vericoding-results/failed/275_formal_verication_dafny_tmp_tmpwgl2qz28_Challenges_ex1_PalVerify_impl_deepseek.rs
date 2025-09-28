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
proof fn lemma_vec_index_properties<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@.index(i) == v[i],
{
}

spec fn is_palindrome(a: &Vec<char>) -> bool {
    forall|i: int| 0 <= i < a.len()/2 ==> a@[i] == a@[a.len() - i - 1]
}

spec fn palindrome_correct(yn: bool, a: &Vec<char>) -> bool {
    yn == is_palindrome(a)
}
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let mut yn: bool = true;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            yn == (forall|j: int| 0 <= j < i ==> a[j] == a[len - j - 1]),
    {
        if a[i] != a[len - i - 1] {
            yn = false;
            break;
        }
        i = i + 1;
    }
    
    proof {
        if yn {
            assert forall|j: int| 0 <= j < len/2 implies a[j] == a[len - j - 1] by {
                if j < i {
                    assert(a[j] == a[len - j - 1]);
                } else {
                    assert(j >= i);
                    assert(i == len/2);
                }
            }
        } else {
            assert(i < len / 2);
            assert(a[i] != a[len - i - 1]);
            assert(exists|j: int| 0 <= j < len/2 && a[j] != a[len - j - 1]) by {
                witness j: int = i;
            };
        }
    }
    
    yn
}
// </vc-code>

fn main() {
}

}