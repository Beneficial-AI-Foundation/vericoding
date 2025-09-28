// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert usize to int for sequence operations */
spec fn usize_to_int(u: usize) -> int { u as int }
/* helper modified by LLM (iteration 4): simple sequence concatenation helper */
spec fn concat_seq(a: Seq<i32>, b: Seq<i32>) -> Seq<i32> { a.add(b) }
// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)

    requires
        first.len() > 0,

    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build res by copying all but last of first then append second, using usize_to_int to convert indices for sequence subrange specs */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < first.len() - 1
        invariant
            i <= first.len() - 1,
            res.len() == i,
            res@ == first@.subrange(0, usize_to_int(i)),
        decreases first.len() - 1 - i
    {
        res.push(first[i]);
        i += 1;
    }
    proof {
        assert(i == first.len() - 1);
        assert(res.len() == i);
        assert(res@ == first@.subrange(0, usize_to_int(i)));
    }
    let mut j: usize = 0;
    while j < second.len()
        invariant
            j <= second.len(),
            res.len() == first.len() - 1 + j,
            res@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, usize_to_int(j))),
        decreases second.len() - j
    {
        res.push(second[j]);
        j += 1;
    }
    res
}
// </vc-code>

}
fn main() {}