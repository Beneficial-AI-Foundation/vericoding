// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_strict(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

/* helper modified by LLM (iteration 2): [fixed Seq::index argument type error by casting usize to int] */
fn find_insertion_point(v: &Vec<i32>, target: i32) -> (pos: usize)
    requires
        is_sorted_strict(v@),
    ensures
        0 <= pos <= v.len(),
        forall|i: int| 0 <= i < pos ==> v@.index(i) < target,
        pos < v.len() ==> v@.index(pos as int) >= target,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            is_sorted_strict(v@),
            forall|j: int| 0 <= j < i ==> v@.index(j) < target,
        decreases v.len() - i
    {
        if v[i] >= target {
            return i;
        }
        i = i + 1;
    }
    i
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(numbers: Vec<i32>) -> (result: usize)
    ensures
        result <= numbers.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [fixed type errors by casting usize to int for Seq::index] */
    let mut tails: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            is_sorted_strict(tails@),
            tails.len() <= i,
        decreases numbers.len() - i
    {
        let num = numbers[i];
        let pos = find_insertion_point(&tails, num);

        if pos == tails.len() {
            proof {
                assert(forall|j: int| 0 <= j < tails.len() ==> tails@.index(j) < num);
            }
            tails.push(num);
        } else {
            proof {
                let old_tails = tails@;
                assert(pos < old_tails.len());
                assert(forall|j: int| 0 <= j < pos ==> old_tails.index(j) < num);
                assert(old_tails.index(pos as int) >= num);
                if pos > 0 {
                    assert(old_tails.index(pos - 1) < num);
                }
                if pos + 1 < old_tails.len() {
                    assert(old_tails.index(pos as int) < old_tails.index((pos + 1) as int));
                }
            }
            tails.set(pos, num);
        }
        i = i + 1;
    }
    tails.len()
}
// </vc-code>

}
fn main() {}