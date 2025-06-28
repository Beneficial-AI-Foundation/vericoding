use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Power(base: int, exp: int) -> int
    recommends exp >= 0
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * Power(base, exp - 1)
    }
}

fn PowerOfListElements(l: Seq<int>, n: int) -> (result: Seq<int>)
    requires
        n >= 0
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> result.spec_index(i) == Power(l.spec_index(i), n)
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == Power(l.spec_index(j), n)
    {
        let powered = power_int(l.spec_index(i as int), n);
        result = result.push(powered);
        
        // Proof that the newly added element satisfies the invariant
        assert(result.len() == i + 1);
        assert(result.spec_index(i as int) == powered);
        assert(powered == Power(l.spec_index(i as int), n));
        
        i = i + 1;
    }
    
    // Final assertions to help verification
    assert(i == l.len());
    assert(result.len() == l.len());
    
    result
}

fn power_int(base: int, exp: int) -> (result: int)
    requires exp >= 0
    ensures result == Power(base, exp)
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let recursive_result = power_int(base, exp - 1);
        assert(recursive_result == Power(base, exp - 1));
        let final_result = base * recursive_result;
        assert(final_result == base * Power(base, exp - 1));
        assert(final_result == Power(base, exp));
        final_result
    }
}

}