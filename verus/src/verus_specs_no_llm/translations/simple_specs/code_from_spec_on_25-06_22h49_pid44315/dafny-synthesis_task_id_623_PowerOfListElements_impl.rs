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
    let mut i: int = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == Power(l.spec_index(j), n)
    {
        let base_val = l.spec_index(i);
        let powered = power_int(base_val, n);
        result = result.push(powered);
        
        // Proof assertion to help with verification
        assert(result.len() == i + 1);
        assert(result.spec_index(i) == powered);
        assert(result.spec_index(i) == Power(l.spec_index(i), n));
        
        i = i + 1;
    }
    
    result
}

fn power_int(base: int, exp: int) -> (result: int)
    requires exp >= 0
    ensures result == Power(base, exp)
    decreases exp
{
    if exp == 0 {
        1int
    } else {
        let sub_result = power_int(base, exp - 1);
        base * sub_result
    }
}

}