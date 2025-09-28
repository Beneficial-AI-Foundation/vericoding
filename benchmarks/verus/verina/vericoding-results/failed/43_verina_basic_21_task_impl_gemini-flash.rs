// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compilation error in `vec_to_int_seq` by removing the `res` keyword from the ensures clause. The `res` keyword is not needed when returning a single type. */
spec fn vec_to_int_seq(v: &Vec<i32>) -> (result: Seq<int>)
    ensures
        result.len() == v.len()
{
    Seq::new(v.len() as nat, |j: int| v[j as usize] as int)
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `is_sublist` function was redesigned, the `assume(false)` and `unreached()` statements were removed, and the core logic now correctly iterates through the `main` vector. If a potential subsequence match is found at index `i`, an inner loop checks for an exact match. Loop invariants and `decreases` clauses have been added and refined to help with verification. The `found_match_at_i` variable helps break out of the inner loop and continue the search. Finally, the function returns `true` if a match is found and `false` otherwise. */
{
    let sub_len = sub.len();
    let main_len = main.len();

    if sub_len == 0 {
        return true;
    }
    if sub_len > main_len {
        return false;
    }

    let mut i: usize = 0;
    while i + sub_len <= main_len
        invariant
            0 <= i as int,
            i <= (main_len - sub_len),
            forall|k: int| 0 <= k < i as int ==> !is_subseq_at(vec_to_int_seq(sub), vec_to_int_seq(main), k as int),
        decreases (main_len - sub_len) - i
    {
        let mut j: usize = 0;
        let mut found_match_at_i = true;

        while j < sub_len
            invariant
                0 <= j as int,
                j <= sub_len as int,
                found_match_at_i ==> forall|k: int| 0 <= k < j as int ==> sub[k as usize] == main[(i + k) as usize],
            decreases sub_len - j
        {
            if main[i + j] != sub[j] {
                found_match_at_i = false;
                break;
            }
            j = j + 1;
        }

        if found_match_at_i {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}