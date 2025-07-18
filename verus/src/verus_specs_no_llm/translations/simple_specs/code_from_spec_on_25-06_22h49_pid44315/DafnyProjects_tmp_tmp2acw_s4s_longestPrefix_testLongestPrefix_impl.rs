use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longest_prefix(a: Vec<int>, b: Vec<int>) -> (i: nat) 
    requires a.len() < usize::MAX && b.len() < usize::MAX
    ensures i <= a@.len() && i <= b@.len()
    ensures forall|k: int| 0 <= k < i ==> a@[k] == b@[k]
    ensures i < a@.len() && i < b@.len() ==> a@[i as int] != b@[i as int]
{
    let mut i: usize = 0;
    let min_len = if a.len() < b.len() { a.len() } else { b.len() };
    
    while i < min_len && i < a.len() && i < b.len()
        invariant 
            i <= min_len,
            min_len <= a.len() && min_len <= b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
            min_len == if a.len() < b.len() { a.len() } else { b.len() },
            i <= a.len() && i <= b.len()
        decreases min_len - i
    {
        if a[i] != b[i] {
            assert(i < a.len() && i < b.len());
            assert(a@[i as int] != b@[i as int]);
            return i as nat;
        }
        i = i + 1;
    }
    
    assert(i <= min_len);
    assert(i <= a.len() && i <= b.len());
    
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
fn test_longest_prefix() -> (result: nat)
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
    
    assert(a@.len() == 3);
    assert(b@.len() == 3);
    assert(a@[0] == 1 && a@[1] == 2 && a@[2] == 3);
    assert(b@[0] == 1 && b@[1] == 2 && b@[2] == 4);
    assert(a@ =~= test_vec_a());
    assert(b@ =~= test_vec_b());
    
    // Establish connection between concrete vectors and spec functions
    assert(forall|k: int| 0 <= k < a@.len() ==> a@[k] == test_vec_a()[k]);
    assert(forall|k: int| 0 <= k < b@.len() ==> b@[k] == test_vec_b()[k]);
    
    let result = longest_prefix(a, b);
    
    // The postcondition of longest_prefix gives us what we need
    assert(result <= a@.len() && result <= b@.len());
    assert(forall|k: int| 0 <= k < result ==> a@[k] == b@[k]);
    
    // Use the established connection to prove the postcondition
    assert(forall|k: int| 0 <= k < result ==> test_vec_a()[k] == test_vec_b()[k]);
    
    result
}

}