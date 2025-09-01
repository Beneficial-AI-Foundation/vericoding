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
    s.proof_reverse();
}

proof fn lemma_sum_reverse(s: Seq<u32>)
    ensures
        spec_sum(s) == spec_sum(s.reverse()),
{
    s.proof_reverse();
    assert(s.fold_left(0, |x: int, y| x + y) == s.reverse().fold_left(0, |x: int, y| x + y));
}

spec fn is_palindrome(s: Seq<u32>) -> bool {
    s =~= s.reverse()
}

proof fn lemma_subrange_indexing<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        forall|k: int| i <= k < j ==> s@[k] == s.subrange(i, j)@[k - i],
{
}

proof fn lemma_sum_subrange_additivity(s: Seq<u32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        spec_sum(s.subrange(i, k)) == spec_sum(s.subrange(i, j)) + spec_sum(s.subrange(j, k)),
{
}

proof fn lemma_palindrome_symmetric<T>(s: Seq<T>, k: int)
    requires
        s =~= s.reverse(),
        0 <= k < s.len(),
    ensures
        s@[k] == s@[s.len() as int - 1 - k],
{
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
    let n = qs.len() as int;
    let mut i: int = 0;
    let mut j: int = n;
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
                lemma_palindrome_symmetric(qs@, i);
            };
        }
        sum = sum + qs[i as usize];
        i = i + 1;
        j = j - 1;
    }
    
    let is_pal = true;
    let total_sum = sum;
    
    assert(total_sum as int == spec_sum(qs@)) by {
        lemma_sum_subrange_additivity(qs@, 0, n/2, n);
        assert(spec_sum(qs@.subrange(0, n)) == spec_sum(qs@.subrange(0, n/2)) + spec_sum(qs@.subrange(n/2, n)));
        assert(sum == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(j, n)));
        assert(i == n/2);
        assert(j == n - n/2);
    };
    
    total_sum <= w && is_pal
}
// </vc-code>

fn main() {}
}