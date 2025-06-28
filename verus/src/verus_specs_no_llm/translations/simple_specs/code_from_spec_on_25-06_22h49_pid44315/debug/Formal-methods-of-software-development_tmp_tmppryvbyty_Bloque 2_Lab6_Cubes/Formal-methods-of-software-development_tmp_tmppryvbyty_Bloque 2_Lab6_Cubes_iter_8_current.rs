use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Cubes(n: int) -> (s: Seq<int>)
    requires
        n >= 0
    ensures
        s.len() == n,
        forall|i: int| 0 <= i < n ==> s.spec_index(i) == i*i*i
{
    let mut result = Seq::empty();
    let mut i: int = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == j*j*j
        decreases n - i
    {
        proof {
            // Help Verus verify that the multiplication is well-defined
            assert(i >= 0);
            assert(i < n);
            // Ensure the cube calculation is correct
            assert(i * i * i == i * i * i);
        }
        
        let cube = i * i * i;
        result = result.push(cube);
        
        proof {
            // Help verify the loop invariant is maintained
            assert(result.len() == i + 1);
            assert(forall|j: int| 0 <= j < i ==> result.spec_index(j) == j*j*j);
            assert(result.spec_index(i) == cube);
            assert(result.spec_index(i) == i*i*i);
        }
        
        i = i + 1;
    }
    
    proof {
        // Final verification that postconditions are met
        assert(i == n);
        assert(result.len() == n);
        assert(forall|j: int| 0 <= j < n ==> result.spec_index(j) == j*j*j);
    }
    
    result
}

}