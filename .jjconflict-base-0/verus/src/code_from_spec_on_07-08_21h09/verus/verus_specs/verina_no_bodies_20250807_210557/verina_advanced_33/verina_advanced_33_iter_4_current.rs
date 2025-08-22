use vstd::prelude::*;

verus! {

spec fn longest_increasing_subsequence_precond(nums: Seq<i32>) -> bool {
    true
}

fn max2(a: usize, b: usize) -> (result: usize)
    ensures result >= a && result >= b && (result == a || result == b)
{
    if a >= b { a } else { b }
}

spec fn is_strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

spec fn all_subsequences(s: Seq<i32>) -> Set<Seq<i32>> {
    Set::new(|subseq: Seq<i32>| 
        exists|indices: Seq<int>| {
            &&& indices.len() == subseq.len()
            &&& (forall|i: int| 0 <= i < indices.len() ==> 0 <= #[trigger] indices[i] < s.len())  
            &&& (forall|i: int, j: int| 0 <= i < j < indices.len() ==> #[trigger] indices[i] < #[trigger] indices[j])
            &&& (forall|i: int| 0 <= i < indices.len() ==> subseq[i] == s[#[trigger] indices[i]])
        }
    )
}

fn helper(lst: Seq<i32>, prev: Option<i32>) -> (result: usize)
    decreases lst.len()
{
    /* code modified by LLM (iteration 1): fixed type casting issue by using proper usize conversion */
    if lst.len() == 0 {
        return 0;
    }
    
    let first = lst[0int];
    let rest = lst.subrange(1int, lst.len());
    
    let without_first = helper(rest, prev);
    
    let with_first = match prev {
        None => 1 + helper(rest, Some(first)),
        Some(p) => {
            if p < first {
                1 + helper(rest, Some(first))
            } else {
                0
            }
        }
    };
    
    max2(without_first, with_first)
}

spec fn longest_increasing_subsequence_postcond(nums: Seq<i32>, result: usize) -> bool {
    let all_subseq = all_subsequences(nums);
    let increasing_subseq_lens = Set::new(|len: int| 
        exists|subseq: Seq<i32>| all_subseq.contains(subseq) && is_strictly_increasing(subseq) && subseq.len() == len
    );
    increasing_subseq_lens.contains(result as int) &&
    (forall|len: int| increasing_subseq_lens.contains(len) ==> len <= result as int)
}

fn longest_increasing_subsequence(nums: Seq<i32>) -> (result: usize)
    requires longest_increasing_subsequence_precond(nums),
    ensures longest_increasing_subsequence_postcond(nums, result),
{
    helper(nums, None)
}

fn main() {
    let example = seq![1i32, 3i32, 2i32, 4i32, 5i32];
    let result = longest_increasing_subsequence(example);
    println!("Length of longest increasing subsequence: {}", result);
}

}