use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_filter_subrange_extend<T>(s: Seq<T>, i: int, pred: spec_fn(T) -> bool)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1).filter(pred) == s.subrange(0, i).filter(pred).push(s[i]).filter(pred)
{
    let left = s.subrange(0, i + 1);
    let right = s.subrange(0, i).push(s[i]);
    assert(left =~= right);
}

proof fn lemma_filter_push<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool)
    ensures s.push(x).filter(pred) == if pred(x) { s.filter(pred).push(x) } else { s.filter(pred) }
{
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut positive_list = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            positive_list@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i,
    {
        proof {
            lemma_filter_subrange_extend(input@, i as int, |x: i32| x > 0);
            lemma_filter_push(input@.subrange(0, i as int), input@[i as int], |x: i32| x > 0);
        }
        
        if input[i] > 0 {
            positive_list.push(input[i]);
        }
        i += 1;
    }
    
    assert(input@.subrange(0, i as int) == input@);
    positive_list
}
// </vc-code>

}
fn main() {}