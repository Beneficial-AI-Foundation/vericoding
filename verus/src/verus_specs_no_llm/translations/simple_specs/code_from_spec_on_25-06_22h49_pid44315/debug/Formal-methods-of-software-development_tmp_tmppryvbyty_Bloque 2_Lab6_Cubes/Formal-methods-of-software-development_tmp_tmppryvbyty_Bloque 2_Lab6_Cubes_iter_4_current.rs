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
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n,
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result.spec_index(j) == j*j*j
    {
        let i_int = i as int;
        result = result.push(i_int * i_int * i_int);
        i = i + 1;
    }
    
    result
}

}