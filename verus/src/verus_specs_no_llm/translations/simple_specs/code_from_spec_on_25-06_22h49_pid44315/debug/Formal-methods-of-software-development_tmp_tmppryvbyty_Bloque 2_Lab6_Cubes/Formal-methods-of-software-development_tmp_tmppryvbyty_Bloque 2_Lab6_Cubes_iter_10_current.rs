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
    let mut result = Seq::<int>::empty();
    let mut i: int = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == j*j*j
        decreases n - i
    {
        let cube = i * i * i;
        result = result.push(cube);
        i = i + 1;
    }
    
    assert(result.len() == n);
    assert(forall|j: int| 0 <= j < n ==> result.spec_index(j) == j*j*j);
    
    result
}

}