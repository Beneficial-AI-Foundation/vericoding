use vstd::prelude::*;

verus! {

proof fn lemma_increasing_sum_params(s: Seq<u32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i <= j <= s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i < j) {
        assert(spec_sum(s.subrange(0, j - 1)) <= spec_sum(s.subrange(0, j))) by {
            assert(s.subrange(0, j).drop_last() == s.subrange(0, j - 1));
        }
        lemma_increasing_sum_params(s, i, j - 1);
    }
    // impl-end
}
// pure-end

proof fn lemma_increasing_sum(s: Seq<u32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
            0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    // post-conditions-end
{
    // impl-start
    assert forall|i: int, j: int|
        #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
        0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)) by {
        if (0 <= i <= j <= s.len()) {
            lemma_increasing_sum_params(s, i, j);
        }
    }
    // impl-end
}
// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

fn sum_lesser_than_limit(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> spec_sum(qs@) <= w,
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

fn palindrome(qs: &Vec<u32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse(),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
