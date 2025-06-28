use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestPrefix(a: Vec<int>, b: Vec<int>) -> (i: nat) 
    requires a.len() < usize::MAX && b.len() < usize::MAX
    ensures i <= a.len() && i <= b.len()
    ensures forall|k: int| 0 <= k < i ==> a[k] == b[k]
    ensures i < a.len() && i < b.len() ==> a[i as int] != b[i as int]
{
    let mut i: usize = 0;
    let min_len = if a.len() < b.len() { a.len() } else { b.len() };
    
    while i < min_len
        invariant 
            i <= min_len,
            min_len <= a.len() && min_len <= b.len(),
            forall|k: int| 0 <= k < i ==> a[k] == b[k]
    {
        if a[i as int] != b[i as int] {
            break;
        }
        i = i + 1;
    }
    
    i as nat
}

// Test method with an example
fn testLongestPrefix() -> (result: nat)
    ensures result <= 3 && result <= 3
    ensures forall|k: int| 0 <= k < result ==> [1, 2, 3][k] == [1, 2, 4][k]
    ensures result < 3 && result < 3 ==> [1, 2, 3][result as int] != [1, 2, 4][result as int]
{
    let a = vec![1, 2, 3];
    let b = vec![1, 2, 4];
    longestPrefix(a, b)
}

}