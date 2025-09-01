use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn intersperse_spec(numbers: Seq<i32>, delim: i32) -> Seq<i32>
    recommends numbers.len() > 0
{
    if numbers.len() == 0 {
        Seq::empty()
    } else {
        let mut result = Seq::empty();
        let mut i = 0;
        while i < numbers.len() {
            if i > 0 {
                result = result.push(delim);
            }
            result = result.push(numbers[i]);
            i += 1;
        }
        result
    }
}

proof fn intersperse_spec_properties(numbers: Seq<i32>, delim: i32)
    ensures
        numbers.len() == 0 ==> intersperse_spec(numbers, delim).len() == 0,
        numbers.len() != 0 ==> intersperse_spec(numbers, delim).len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < intersperse_spec(numbers, delim).len() && i % 2 == 0 ==> 
            intersperse_spec(numbers, delim)[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < intersperse_spec(numbers, delim).len() && i % 2 == 1 ==> 
            intersperse_spec(numbers, delim)[i] == delim
{
    if numbers.len() == 0 {
        assert(intersperse_spec(numbers, delim).len() == 0);
    } else {
        let mut result = Seq::empty();
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= j <= numbers.len(),
                result.len() == (if j == 0 then 0 else 2*j - 1),
                forall|k: int| 0 <= k && k < result.len() && k % 2 == 0 ==> result[k] == numbers[k / 2],
                forall|k: int| 0 <= k && k < result.len() && k % 2 == 1 ==> result[k] == delim
        {
            if j > 0 {
                result = result.push(delim);
            }
            result = result.push(numbers[j]);
            j += 1;
        }
        assert(result =~= intersperse_spec(numbers, delim));
    }
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
    let mut res = Vec::new();
    let n = numbers.len();
    
    if n == 0 {
        assert(res@.len() == 0);
        res
    } else {
        proof { intersperse_spec_properties(numbers@, delim); }
        
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                res@.len() == (if i == 0 then 0 else 2*i - 1),
                forall|k: int| 0 <= k && k < res@.len() && k % 2 == 0 ==> res@[k] == numbers@[k / 2],
                forall|k: int| 0 <= k && k < res@.len() && k % 2 == 1 ==> res@[k] == delim
        {
            if i > 0 {
                res.push(delim);
                assert(res@.len() == 2*i - 1);
                assert(res@[res@.len() - 1] == delim);
            }
            res.push(numbers[i]);
            assert(res@.len() == 2*i + 1);
            assert(res@[res@.len() - 1] == numbers[i]);
            i += 1;
        }
        
        assert(res@.len() == 2*n - 1);
        res
    }
}
// </vc-code>

fn main() {}
}