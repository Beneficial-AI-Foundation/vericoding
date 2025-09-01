use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove division properties
proof fn lemma_div_properties(i: int, n: int)
    requires
        0 <= i < 2 * n - 1,
        i % 2 == 0,
        n > 0,
    ensures
        0 <= i / 2 < n,
{
    assert(i >= 0);
    assert(i < 2 * n - 1);
    assert(i % 2 == 0);
    assert(i / 2 >= 0);
    assert(i <= 2 * n - 2);
    assert(i / 2 <= (2 * n - 2) / 2);
    assert(i / 2 <= n - 1);
    assert(i / 2 < n);
}

// Helper lemma for odd indices
proof fn lemma_odd_index_bounds(i: int, n: int)
    requires
        0 <= i < 2 * n - 1,
        i % 2 == 1,
        n > 0,
    ensures
        i >= 1,
{
    assert(i % 2 == 1);
    assert(i >= 1);
}
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    // post-conditions-start
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if numbers.len() == 0 {
        return vec![];
    }
    
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            numbers.len() > 0,
            res.len() == if i == 0 { 0 } else { 2 * i - 1 },
            forall|j: int| 0 <= j < res.len() && j % 2 == 0 ==> res[j] == numbers[j / 2],
            forall|j: int| 0 <= j < res.len() && j % 2 == 1 ==> res[j] == delim,
    {
        if i > 0 {
            res.push(delim);
            assert(res.len() == 2 * i);
            assert(res.len() - 1 == 2 * i - 1);
            assert((res.len() - 1) % 2 == 1);
        }
        
        res.push(numbers[i]);
        
        proof {
            let new_len = res.len() as int;
            let even_idx = new_len - 1;
            assert(even_idx % 2 == 0);
            assert(even_idx / 2 == i);
            
            // Prove the even index property still holds
            assert(forall|j: int| 0 <= j < new_len && j % 2 == 0 ==> res[j] == numbers[j / 2]);
        }
        
        i += 1;
    }
    
    proof {
        if numbers.len() > 0 {
            assert(res.len() == 2 * numbers.len() - 1);
            
            // Apply lemmas to prove final postconditions
            assert(forall|j: int| 0 <= j < res.len() && j % 2 == 0 ==> {
                proof {
                    lemma_div_properties(j, numbers.len() as int);
                }
                res[j] == numbers[j / 2]
            });
            
            assert(forall|j: int| 0 <= j < res.len() && j % 2 == 1 ==> {
                proof {
                    lemma_odd_index_bounds(j, numbers.len() as int);
                }
                res[j] == delim
            });
        }
    }
    
    res
}
// </vc-code>

fn main() {}
}