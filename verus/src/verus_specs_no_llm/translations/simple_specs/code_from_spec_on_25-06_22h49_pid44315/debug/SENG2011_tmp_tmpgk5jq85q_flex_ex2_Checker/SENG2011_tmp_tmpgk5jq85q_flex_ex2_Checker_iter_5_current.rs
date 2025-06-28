use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(s: Vec<nat>) -> (a: nat)
    requires 
        s.len() > 0
    ensures 
        forall|x: int| 0 <= x < s.len() ==> a >= s[x as int],
        exists|i: int| 0 <= i < s.len() && a == s[i as int]
{
    let mut max_val = s[0];
    let mut i: usize = 1;
    let mut max_index: usize = 0;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            s.len() > 0,
            0 <= max_index < i,
            max_val == s[max_index as int],
            forall|k: int| 0 <= k < i ==> max_val >= s[k as int]
    {
        if s[i] > max_val {
            max_val = s[i];
            max_index = i;
        }
        i = i + 1;
    }
    
    // Proof that max_val satisfies the postcondition
    assert(max_val == s[max_index as int]);
    assert(forall|k: int| 0 <= k < s.len() ==> max_val >= s[k as int]);
    assert(exists|j: int| 0 <= j < s.len() && max_val == s[j as int]) by {
        assert(0 <= max_index < s.len());
        assert(max_val == s[max_index as int]);
    }
    
    max_val
}

// Helper spec function to work with sequences
spec fn seq_max(s: Seq<nat>) -> nat
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = seq_max(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
    }
}

// Alternative implementation using sequence operations
fn max_seq(s: &Vec<nat>) -> (a: nat)
    requires 
        s.len() > 0
    ensures 
        forall|x: int| 0 <= x < s.len() ==> a >= s[x as int],
        exists|i: int| 0 <= i < s.len() && a == s[i as int]
{
    let mut max_val = s[0];
    let mut i: usize = 1;
    let mut max_index: usize = 0;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            s.len() > 0,
            0 <= max_index < i,
            max_val == s[max_index as int],
            forall|k: int| 0 <= k < i ==> max_val >= s[k as int]
    {
        if s[i] > max_val {
            max_val = s[i];
            max_index = i;
        }
        i = i + 1;
    }
    
    // Proof that max_val satisfies the postcondition
    assert(max_val == s[max_index as int]);
    assert(forall|k: int| 0 <= k < s.len() ==> max_val >= s[k as int]);
    assert(exists|j: int| 0 <= j < s.len() && max_val == s[j as int]) by {
        assert(0 <= max_index < s.len());
        assert(max_val == s[max_index as int]);
    }
    
    max_val
}

// Test function to verify the implementation  
fn test_max()
{
    let mut v = Vec::<nat>::new();
    v.push(1);
    v.push(3);
    v.push(2);
    
    let result = max_seq(&v);
    assert(result == 3);
}

}