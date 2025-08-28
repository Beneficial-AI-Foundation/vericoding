use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
fn sum_lesser_than_limit(qs: &Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret <==> spec_sum(qs@) <= w,
{
    let mut sum: u32 = 0;
    for i in 0..qs.len()
        invariant
            sum == spec_sum(qs@.subrange(0, i as int)),
            i <= qs.len(),
            sum <= w,
    {
        proof {
            assert(spec_sum(qs@.subrange(0, i + 1)) <= spec_sum(qs@)) by {
                assert(qs@ == qs@.subrange(0, qs@.len() as int));
                lemma_increasing_sum(qs@);
            }
            assert(spec_sum(qs@.subrange(0, i as int)) + qs[i as int] == spec_sum(
                qs@.subrange(0, i + 1),
            )) by {
                assert(qs@.subrange(0, i + 1).drop_last() == qs@.subrange(0, i as int));
            }
        }
        let sum_opt = sum.checked_add(qs[i]);
        if sum_opt.is_none() {
            assert(spec_sum(qs@.subrange(0, i + 1)) > u32::MAX >= w);
            return false;
        } else {
            sum = sum_opt.unwrap();
            if sum > w {
                assert(spec_sum(qs@.subrange(0, i + 1)) > w);
                return false;
            }
        }
    }
    true
}

fn palindrome(qs: &Vec<u32>) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse(),
{
    let mut ret = true;
    let mut i: usize = 0;
    while i < qs.len() / 2
        invariant
            i <= qs@.len() / 2,
            ret <==> qs@.subrange(0, i as int) =~= qs@.subrange(
                qs@.len() - i,
                qs@.len() as int,
            ).reverse(),
        decreases qs.len() / 2 - i,
    {
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse().drop_last()
            =~= qs@.subrange(qs@.len() - i, qs@.len() as int).reverse());
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse() =~= qs@.subrange(
            qs@.len() - i,
            qs@.len() as int,
        ).reverse().push(qs@.index(qs@.len() - (i + 1))));
        if qs[i] != qs[qs.len() - i - 1] {
            ret = false;
        }
        i += 1;
    }
    let ghost fst_half = qs@.subrange(0, (qs@.len() / 2) as int);
    let ghost snd_half = qs@.subrange(qs@.len() - qs@.len() / 2, qs@.len() as int);
    proof {
        if (qs.len() % 2) == 1 {
            assert(qs@ =~= fst_half + qs@.subrange(
                (qs@.len() / 2) as int,
                qs@.len() - qs@.len() / 2,
            ) + snd_half);
        } else {
            assert(qs@ =~= fst_half + snd_half);
        }
    }
    ret
}

proof fn lemma_increasing_sum_params(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    decreases j - i,
{
    if (i < j) {
        assert(spec_sum(s.subrange(0, j - 1)) <= spec_sum(s.subrange(0, j))) by {
            assert(s.subrange(0, j).drop_last() == s.subrange(0, j - 1));
        }
        lemma_increasing_sum_params(s, i, j - 1);
    }
}

proof fn lemma_increasing_sum(s: Seq<u32>)
    ensures
        forall|i: int, j: int|
            #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
            0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
{
    assert forall|i: int, j: int|
        #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
        0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)) by {
        if (0 <= i <= j <= s.len()) {
            lemma_increasing_sum_params(s, i, j);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
{
    let is_palindrome = palindrome(qs);
    let is_under_limit = sum_lesser_than_limit(qs, w);
    is_palindrome && is_under_limit
}
// </vc-code>

}
fn main() {}