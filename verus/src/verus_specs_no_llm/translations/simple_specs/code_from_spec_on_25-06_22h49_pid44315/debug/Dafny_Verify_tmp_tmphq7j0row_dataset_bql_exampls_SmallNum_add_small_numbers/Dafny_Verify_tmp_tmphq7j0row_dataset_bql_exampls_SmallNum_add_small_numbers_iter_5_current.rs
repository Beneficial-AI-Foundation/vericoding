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
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            i <= a.len(),
            n_usize == n,
            sum <= max * (i as int),
            (forall j: int :: 0 <= j && j < n ==> a.spec_index(j) <= max),
            n <= a.len()
    {
        assert(i < n_usize);
        assert(i < a.len());
        assert((i as int) < n);
        assert(a.spec_index(i as int) <= max);
        
        sum = sum + a[i];
        i = i + 1;
        
        assert(sum <= max * (i as int));
    }
    
    assert(i == n_usize);
    assert((i as int) == n);
    assert(sum <= max * n);
    
    sum
}

}