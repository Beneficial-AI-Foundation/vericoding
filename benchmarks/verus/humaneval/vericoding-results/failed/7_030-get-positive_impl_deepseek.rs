// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove exec mode is_positive and fix lemmas to use proper closure syntax */
fn is_positive(x: i32) -> bool { x > 0 }

proof fn filter_lemma(s: Seq<i32>) 
    ensures 
        s.filter(|x: i32| x > 0) == s.filter(|x: i32| is_positive(x)),
{
}

proof fn filter_empty_lemma() 
    ensures 
        Seq::<i32>::empty().filter(|x: i32| x > 0) == Seq::<i32>::empty().filter(|x: i32| is_positive(x)),
{
}

proof fn filter_cons_lemma(x: i32, s: Seq<i32>) 
    ensures 
        s.insert(0, x).filter(|y: i32| y > 0) == if x > 0 {
            s.filter(|y: i32| y > 0).insert(0, x)
        } else {
            s.filter(|y: i32| y > 0)
        },
{
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use direct comparison x > 0 instead of is_positive function in exec mode */
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < input.len()
        invariant
            i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i,
    {
        let elem = input[i];
        if elem > 0 {
            result.push(elem);
        }
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}