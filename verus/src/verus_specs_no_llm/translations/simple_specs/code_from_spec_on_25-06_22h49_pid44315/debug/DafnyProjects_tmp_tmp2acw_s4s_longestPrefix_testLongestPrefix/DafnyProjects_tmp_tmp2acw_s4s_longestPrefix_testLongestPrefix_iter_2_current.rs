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
            forall|k: int| 0 <= k < i ==> a[k] == b[k],
            (min_len == a.len() || min_len == b.len()),
            min_len == if a.len() < b.len() { a.len() } else { b.len() }
    {
        if a[i as int] != b[i as int] {
            // Prove that we satisfy the postcondition when breaking early
            assert(i < a.len() && i < b.len());
            assert(a[i as int] != b[i as int]);
            break;
        }
        i = i + 1;
    }
    
    // After the loop, either i == min_len or we broke early
    // If i == min_len, then either i == a.len() or i == b.len() (or both)
    // In that case, the condition i < a.len() && i < b.len() is false
    // So the implication in the postcondition is vacuously true
    
    i as nat
}

// Helper spec function to represent a test vector
spec fn test_vec_a() -> Seq<int> {
    seq![1int, 2int, 3int]
}

spec fn test_vec_b() -> Seq<int> {
    seq![1int, 2int, 4int]
}

// Test method with an example
fn testLongestPrefix() -> (result: nat)
    ensures result <= 3 && result <= 3
    ensures forall|k: int| 0 <= k < result ==> test_vec_a()[k] == test_vec_b()[k]
    ensures result < 3 && result < 3 ==> test_vec_a()[result as int] != test_vec_b()[result as int]
{
    let mut a: Vec<int> = Vec::new();
    a.push(1);
    a.push(2);
    a.push(3);
    
    let mut b: Vec<int> = Vec::new();
    b.push(1);
    b.push(2);
    b.push(4);
    
    // Prove that our constructed vectors match the spec
    assert(a@ == test_vec_a());
    assert(b@ == test_vec_b());
    
    let result = longestPrefix(a, b);
    
    // The postconditions of longestPrefix give us what we need
    assert(forall|k: int| 0 <= k < result ==> a@[k] == b@[k]);
    assert(result < a@.len() && result < b@.len() ==> a@[result as int] != b@[result as int]);
    
    result
}

}