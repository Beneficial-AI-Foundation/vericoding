use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
}

proof fn abs_diff_commutative(a: int, b: int)
    ensures abs_diff(a, b) == abs_diff(b, a)
{
    if a - b < 0 {
        assert(b - a > 0);
        assert(abs_diff(a, b) == b - a);
        assert(abs_diff(b, a) == b - a);
    } else {
        assert(a - b >= 0);
        assert(abs_diff(a, b) == a - b);
        if b - a < 0 {
            assert(abs_diff(b, a) == a - b);
        } else {
            assert(b - a == 0);
            assert(a == b);
            assert(abs_diff(b, a) == 0);
            assert(abs_diff(a, b) == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (res: bool)
    requires threshold >= 0,
    ensures ({
        &&& (res ==> exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers[i], numbers[j]) < threshold)
        &&& (!res ==> forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold)
    }),
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    if n <= 1nat {
        return false;
    }
    
    for i in 1..n as int
        invariant
            forall|ii: int, jj: int| 1 <= ii < i && 0 <= jj < ii ==> 
                abs_diff(numbers[ii], numbers[jj]) >= threshold
    {
        for j in 0..i as int
            invariant
                forall|ii: int, jj: int| 1 <= ii < i && 0 <= jj < ii ==> 
                    abs_diff(numbers[ii], numbers[jj]) >= threshold,
                forall|jj: int| 0 <= jj < j ==> 
                    abs_diff(numbers[i as int], numbers[jj]) >= threshold
        {
            let diff = if numbers[i as int] < numbers[j as int] {
                numbers[j as int] - numbers[i as int]
            } else {
                numbers[i as int] - numbers[j as int]
            };
            
            proof {
                assert(diff == abs_diff(numbers[i as int], numbers[j as int]));
            }
            
            if diff < threshold {
                proof {
                    assert(i != j);
                    assert(0 <= i < numbers.len());
                    assert(0 <= j < numbers.len());
                    assert(abs_diff(numbers[i as int], numbers[j as int]) < threshold);
                }
                return true;
            }
        }
    }
    
    proof {
        assert(forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold);
    }
    false
}
// </vc-code>

fn main() {
}

}