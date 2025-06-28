use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total(a.spec_index(0..a.len()))
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == total(a.spec_index(0..i as int))
    {
        sum = sum + a.spec_index(i as int);
        i = i + 1;
    }
    
    sum
}

}