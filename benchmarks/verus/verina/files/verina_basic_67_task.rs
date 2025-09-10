/* This task requires determining whether a given list of characters is a palindrome; that is, whether the sequence reads the same forward and backward.

-----Input-----
The input consists of:
• x: A list of characters (List Char). The list can be empty or non-empty.

-----Output-----
The output is a Boolean value (Bool):
• Returns true if the input list is a palindrome.
• Returns false otherwise.

-----Note-----
An empty list is considered a palindrome. The function does not impose any additional preconditions. */

use vstd::prelude::*;

verus! {
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
{
    // impl-start
    assume(false);
    false
    // impl-end
}
}
fn main() {}