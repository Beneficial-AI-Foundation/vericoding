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
        // First establish that we can access a[i]
        assert(i < a.len());
        
        // Prove the relationship step by step
        let old_sum = sum;
        let old_i = i as int;
        
        if a[i] < 0 {
            sum = sum + a[i];
        }
        i = i + 1;
        
        // Now prove that the new sum equals sumNegativesTo(a, new_i)
        let new_i = i as int;
        assert(new_i == old_i + 1);
        assert(new_i > 0);
        
        // By definition of sumNegativesTo
        assert(sumNegativesTo(a, new_i) == {
            let prev = sumNegativesTo(a, new_i - 1);
            if a[new_i - 1] < 0 {
                prev + a[new_i - 1]
            } else {
                prev
            }
        });
        
        // Since new_i - 1 == old_i and a[new_i - 1] == a[old_i as usize]
        assert(new_i - 1 == old_i);
        assert(old_i as usize == (i - 1));
        assert(a[new_i - 1] == a[i - 1]);
        
        // Connect the pieces
        assert(sumNegativesTo(a, old_i) == old_sum);
        
        if a[i - 1] < 0 {
            assert(sum == old_sum + a[i - 1]);
            assert(sumNegativesTo(a, new_i) == sumNegativesTo(a, old_i) + a[new_i - 1]);
            assert(sum == sumNegativesTo(a, new_i));
        } else {
            assert(sum == old_sum);
            assert(sumNegativesTo(a, new_i) == sumNegativesTo(a, old_i));
            assert(sum == sumNegativesTo(a, new_i));
        }
    }
    
    sum
}

}