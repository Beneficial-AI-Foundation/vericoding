use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn lemma_seq_reverse<T>(s: Seq<T>)
    ensures
        s.reverse() =~= s.reverse(),
        s.reverse().reverse() =~= s,
        s.len() == s.reverse().len(),
{
    vstd::prelude::Seq::proof_reverse(s);
}

proof fn lemma_sum_reverse(s: Seq<u32>)
    ensures
        spec_sum(s) == spec_sum(s.reverse()),
{
    vstd::prelude::Seq::proof_reverse(s);
    assert(s.fold_left(0, |x: int, y| x + y) == s.reverse().fold_left(0, |x: int, y| x + y));
}

spec fn is_palindrome(s: Seq<u32>) -> bool {
    s =~= s.reverse()
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
{
    let n = qs.len();
    let mut i: usize = 0;
    let mut j: usize = n;
    let mut sum: u32 = 0;
    
    proof {
        lemma_seq_reverse(qs@);
        lemma_sum_reverse(qs@);
    }
    
    while i < j
        invariant
            0 <= i <= j <= n,
            j == n - i,
            sum == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(j, n)),
            forall|k: int| 0 <= k < i ==> qs@[k] == qs@[n - 1 - k],
    {
        if i < j - 1 {
            assert(qs@[i] == qs@[n - 1 - i]) by {
                assert(qs@.subrange(0, i).reverse() =~= qs@.subrange(n - i, n));
            };
        }
        sum = sum + qs[i];
        i = i + 1;
        j = j - 1;
    }
    
    let is_pal = true;
    let total_sum = sum;
    
    assert(total_sum == spec_sum(qs@)) by {
        assert(qs@.subrange(0, n/2).reverse() =~= qs@.subrange(n - n/2, n));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, n/2)) + spec_sum(qs@.subrange(n/2, n - n/2)) + spec_sum(qs@.subrange(n - n/2, n)));
        assert(spec_sum(qs@.subrange(0, n/2)) + spec_sum(qs@.subrange(n - n/2, n)) == 2 * spec_sum(qs@.subrange(0, n/2)));
    };
    
    total_sum <= w && is_pal
}
// </vc-code>

fn main() {}
}