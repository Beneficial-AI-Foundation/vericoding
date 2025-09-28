use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
spec fn pair_in_range(s: Seq<int>, start: int, end: int, threshold: int) -> bool {
    exists|i: int, j: int| 
        start <= i < end && 
        start <= j < end && 
        i != j && 
        abs(s[i] - s[j]) < threshold
}

proof fn lemma_has_close_elements_recursive(s: Seq<int>, start: int, end: int, threshold: int)
    ensures
        start < end <= s.len() ==>
        (pair_in_range(s, start, end, threshold) <==>
            pair_in_range(s, start, end - 1, threshold) ||
            exists|j: int| start <= j < end - 1 && abs(s[j] - s[end - 1]) < threshold)
{
    if start < end && end <= s.len() {
        assert forall|i: int, j: int|
            start <= i < end && start <= j < end && i != j implies
            (i < end - 1 && j < end - 1 && pair_in_range(s, start, end - 1, threshold)) ||
            (i == end - 1 && start <= j < end - 1) ||
            (j == end - 1 && start <= i < end - 1)
        by {
            if start <= i < end && start <= j < end && i != j {
                if i != end - 1 && j != end - 1 {
                    assert(pair_in_range(s, start, end - 1, threshold));
                }
            }
        };
    }
}

spec fn pair_in_range_nat(s: Seq<int>, start: nat, end: nat, threshold: int) -> bool 
    recommends start <= end <= s.len()
{
    pair_in_range(s, start as int, end as int, threshold)
}

spec fn exists_k_abs_lt(s: Seq<int>, i: nat, j: nat, threshold: int) -> bool 
    recommends i < s.len() && j <= i
{
    exists|k: nat| k < j && abs(s[k] - s[i]) < threshold
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
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            i == 0 ==> !pair_in_range_nat(numbers, 0, i, threshold),
            i > 0 ==> (pair_in_range_nat(numbers, 0, i, threshold) <==> 
                      exists|k: nat, l: nat| k < i && l < i && k != l && abs(numbers[k] - numbers[l]) < threshold),
    {
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                j == 0 ==> !exists_k_abs_lt(numbers, i, i, threshold),
                j > 0 ==> (exists_k_abs_lt(numbers, i, i, threshold) <==>
                         (exists_k_abs_lt(numbers, i, j, threshold) ||
                         abs(numbers[j - 1] - numbers[i]) < threshold)),
        {
            proof {
                let diff = abs(numbers@[j] - numbers@[i]);
                if diff < threshold {
                    assert(exists_k_abs_lt(numbers, i, j + 1, threshold));
                }
            }
            if abs(numbers@[j] - numbers@[i]) < threshold {
                return true;
            }
            j = j + 1;
        }
        
        proof {
            lemma_has_close_elements_recursive(numbers, 0, (i + 1) as int, threshold);
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

fn main() {}

}