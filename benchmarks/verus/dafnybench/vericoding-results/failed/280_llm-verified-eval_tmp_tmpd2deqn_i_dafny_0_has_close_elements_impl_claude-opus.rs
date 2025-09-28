use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
spec fn abs_i64(x: i64) -> i64 {
    if x < 0 { -x } else { x }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// <vc-code>
{
    if numbers.len() <= 1 {
        return false;
    }
    
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|a: int, b: int| 
                0 <= a < i as int && 0 <= b < numbers.len() && a != b ==> 
                abs(#[trigger] numbers[a] - numbers[b]) >= threshold
    {
        for j in 0..n
            invariant
                forall|b: int| 
                    0 <= b < j as int && i as int != b ==> 
                    abs(#[trigger] numbers[i as int] - numbers[b]) >= threshold,
                forall|a: int, b: int| 
                    0 <= a < i as int && 0 <= b < numbers.len() && a != b ==> 
                    abs(#[trigger] numbers[a] - numbers[b]) >= threshold
        {
            if i != j {
                proof {
                    assert(0 <= i < numbers.len());
                    assert(0 <= j < numbers.len());
                }
                
                let ni = numbers[i as int];
                let nj = numbers[j as int];
                let diff = if ni < nj {
                    nj - ni
                } else {
                    ni - nj
                };
                
                if diff < threshold {
                    proof {
                        assert(i as int != j as int);
                        assert(abs(numbers[i as int] - numbers[j as int]) == diff);
                        assert(abs(numbers[i as int] - numbers[j as int]) < threshold);
                    }
                    return true;
                }
            }
        }
    }
    
    proof {
        assert(forall|a: int, b: int| 
            0 <= a < numbers.len() && 0 <= b < numbers.len() && a != b ==> 
            abs(#[trigger] numbers[a] - numbers[b]) >= threshold);
    }
    
    false
}
// </vc-code>

fn main() {}

}