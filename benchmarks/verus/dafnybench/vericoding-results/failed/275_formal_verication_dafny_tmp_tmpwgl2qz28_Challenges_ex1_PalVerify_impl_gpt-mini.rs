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
// Updated helpers: no additional helpers required for this proof, kept minimal.
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]
    ensures yn == false ==> exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n / 2 {
        invariant 0 <= i && i <= n / 2;
        invariant n == a.len() as int;
        invariant forall|j: int| 0 <= j && j < i ==> #[trigger] a[j as nat] == #[trigger] a[(n - j - 1) as nat];
        if a[i as nat] != a[(n - i - 1) as nat] {
            proof {
                let k: int = i;
                assert(0 <= k && k < n / 2);
                // Provide witness k for the existential required by the postcondition
                exists(k);
                assert(a[k as nat] != a[(n - k - 1) as nat]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        // On loop exit, i >= n/2 and invariant gives i <= n/2, so i == n/2
        assert(i == n / 2);
        assert(forall|j: int| 0 <= j && j < i ==> a[j as nat] == a[(n - j - 1) as nat]);
        assert(forall|j: int| 0 <= j && j < n / 2 ==> a[j as nat] == a[(n - j - 1) as nat]);
    }
    return true;
}
// </vc-code>

fn main() {
}

}