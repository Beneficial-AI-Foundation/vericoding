use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumNegativesTo(a: Vec<int>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        let prev = sumNegativesTo(a, i - 1);
        if a[i - 1] < 0 {
            prev + a[i - 1]
        } else {
            prev
        }
    }
}

fn SumOfNegatives(a: Vec<int>) -> (result: int)
    ensures
        result == sumNegativesTo(a, a.len() as int)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sumNegativesTo(a, i as int)
    {
        if a[i] < 0 {
            sum = sum + a[i];
        }
        i = i + 1;
        
        // Proof hint to help Verus understand the loop invariant
        assert(sum == sumNegativesTo(a, i as int)) by {
            if i > 0 {
                assert(a[(i-1) as usize] == a[i as int - 1]);
            }
        };
    }
    
    sum
}

}