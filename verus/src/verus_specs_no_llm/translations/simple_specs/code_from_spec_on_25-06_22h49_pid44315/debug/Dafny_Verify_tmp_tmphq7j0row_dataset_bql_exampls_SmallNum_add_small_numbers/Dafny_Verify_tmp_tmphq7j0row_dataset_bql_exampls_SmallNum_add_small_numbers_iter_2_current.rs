use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_small_numbers(a: Vec<int>, n: int, max: int) -> (r: int)
    requires
        n > 0,
        n <= a.len(),
        (forall i: int :: 0 <= i && i < n ==> a.spec_index(i) <= max)
    ensures
        r <= max * n
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i && i <= n,
            sum <= max * i,
            (forall j: int :: 0 <= j && j < n ==> a.spec_index(j) <= max)
    {
        assert(i < n);
        assert(0 <= i && i < a.len());
        assert(a.spec_index(i) <= max);
        
        sum = sum + a[i as usize];
        i = i + 1;
        
        assert(sum <= max * i);
    }
    
    assert(i == n);
    assert(sum <= max * n);
    sum
}

}