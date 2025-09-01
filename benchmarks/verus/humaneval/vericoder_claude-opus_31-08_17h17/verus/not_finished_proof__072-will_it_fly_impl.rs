use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn lemma_sum_bounds(s: Seq<u32>)
    ensures
        0 <= spec_sum(s) <= s.len() * u32::MAX,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s =~= Seq::<u32>::empty());
        assert(spec_sum(s) == 0);
    } else {
        let s_init = s.drop_last();
        lemma_sum_bounds(s_init);
        assert(s =~= s_init.push(s[s.len() - 1]));
        assert(spec_sum(s) == spec_sum(s_init) + s[s.len() - 1]);
        assert(s[s.len() - 1] <= u32::MAX);
    }
}

fn compute_sum(qs: &Vec<u32>) -> (ret: u64)
    requires
        spec_sum(qs@) <= u64::MAX,
    ensures
        ret == spec_sum(qs@),
{
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_sum_bounds(qs@);
    }
    
    while i < qs.len()
        invariant
            0 <= i <= qs.len(),
            sum == spec_sum(qs@.take(i as int)),
            spec_sum(qs@.take(i as int)) <= spec_sum(qs@),
        decreases qs.len() - i,
    {
        proof {
            lemma_sum_bounds(qs@.take(i as int));
            lemma_sum_bounds(qs@.take((i + 1) as int));
            assert(qs@.take((i + 1) as int) =~= qs@.take(i as int).push(qs@[i as int]));
            assert(spec_sum(qs@.take((i + 1) as int)) == spec_sum(qs@.take(i as int)) + qs@[i as int]);
            assert(spec_sum(qs@.take((i + 1) as int)) <= spec_sum(qs@));
        }
        sum = sum + qs[i] as u64;
        i = i + 1;
    }
    
    proof {
        assert(qs@.take(qs.len() as int) =~= qs@);
    }
    
    sum
}

fn is_palindrome(qs: &Vec<u32>) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse(),
{
    let n = qs.len();
    let mut i: usize = 0;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] qs@[j] == qs@[n as int - 1 - j],
        decreases n / 2 - i,
    {
        if qs[i] != qs[n - 1 - i] {
            proof {
                assert(qs@[i as int] != qs@[n as int - 1 - i as int]);
                assert(qs@ =~= qs@.reverse() ==> qs@[i as int] == qs@.reverse()[i as int]);
                assert(qs@.reverse()[i as int] == qs@[n as int - 1 - i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert forall|j: int| 0 <= j < n implies qs@[j] == qs@.reverse()[j] by {
            if j < n / 2 {
                assert(qs@[j] == qs@[n as int - 1 - j]);
                assert(qs@.reverse()[j] == qs@[n as int - 1 - j]);
            } else if j >= (n + 1) / 2 {
                let k = n as int - 1 - j;
                assert(0 <= k < n / 2);
                assert(qs@[k] == qs@[n as int - 1 - k]);
                assert(qs@[j] == qs@[n as int - 1 - k]);
                assert(qs@.reverse()[j] == qs@[k]);
            } else {
                assert(n % 2 == 1);
                assert(j == n / 2);
                assert(qs@.reverse()[j] == qs@[j]);
            }
        }
        assert(qs@ =~= qs@.reverse());
    }
    
    true
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
    let is_pal = is_palindrome(qs);
    if !is_pal {
        return false;
    }
    
    proof {
        lemma_sum_bounds(qs@);
    }
    
    if spec_sum(qs@) > u64::MAX {
        // Sum is too large to compute, definitely > w
        return false;
    }
    
    let sum = compute_sum(qs);
    
    proof {
        assert(sum == spec_sum(qs@));
    }
    
    sum <= w as u64
}
// </vc-code>

fn main() {}
}