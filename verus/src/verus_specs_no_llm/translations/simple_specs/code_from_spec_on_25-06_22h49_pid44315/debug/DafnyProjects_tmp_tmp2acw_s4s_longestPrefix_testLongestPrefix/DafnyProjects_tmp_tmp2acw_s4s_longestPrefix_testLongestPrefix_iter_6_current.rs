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
    
    while i < min_len
        invariant 
            i <= min_len,
            min_len <= a.len() && min_len <= b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
            min_len == if a.len() < b.len() { a.len() } else { b.len() },
            i <= a.len() && i <= b.len()
    {
        if a[i] != b[i] {
            // At this point we know a[i] != b[i], so the postcondition is satisfied
            proof {
                assert(i < a.len() && i < b.len());
                assert(a@[i as int] != b@[i as int]);
            }
            return i as nat;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == min_len
    // This means either i == a.len() or i == b.len() (or both)
    // So the condition i < a.len() && i < b.len() is false
    proof {
        assert(i == min_len);
        assert(min_len == if a.len() < b.len() { a.len() } else { b.len() });
        if a.len() < b.len() {
            assert(i == a.len());
            assert(!(i < a.len() && i < b.len()));
        } else {
            assert(i == b.len());
            assert(!(i < a.len() && i < b.len()));
        }
    }
    
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
    
    // Prove that our constructed vectors match the spec
    proof {
        assert(a@.len() == 3);
        assert(b@.len() == 3);
        assert(a@[0] == 1 && a@[1] == 2 && a@[2] == 3);
        assert(b@[0] == 1 && b@[1] == 2 && b@[2] == 4);
        assert(a@ =~= test_vec_a());
        assert(b@ =~= test_vec_b());
    }
    
    let result = longest_prefix(a, b);
    
    // Additional proof to help verification
    proof {
        assert(result == 2);
        assert(test_vec_a()[0] == test_vec_b()[0]); // both are 1
        assert(test_vec_a()[1] == test_vec_b()[1]); // both are 2
        assert(test_vec_a()[2] != test_vec_b()[2]); // 3 != 4
        assert(forall|k: int| 0 <= k < result ==> test_vec_a()[k] == test_vec_b()[k]);
        assert(result < 3 && result < 3);
        assert(test_vec_a()[result as int] != test_vec_b()[result as int]);
    }
    
    result
}

}