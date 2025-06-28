use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPalindrome(a: Seq<char>) -> (b: bool)
{
    let len = a.len();
    if len <= 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|k: int| 0 <= k < i ==> a[k] == a[len - 1 - k],
    {
        if a[i as int] != a[len - 1 - (i as int)] {
            return false;
        }
        i = i + 1;
    }
    
    true
}

}