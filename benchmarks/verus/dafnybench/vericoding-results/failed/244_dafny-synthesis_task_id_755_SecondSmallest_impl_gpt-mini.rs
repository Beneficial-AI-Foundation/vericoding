use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
spec fn min(s: Seq<i32>) -> i32
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail = min(s[1..]);
        if s[0] <= tail { s[0] } else { tail }
    }
}

proof fn min_is_min(s: Seq<i32>)
    requires s.len() >= 1
    ensures forall|k: int| 0 <= k && k < s.len() as int ==> min(s) <= s[k as usize]
    ensures exists|k: int| 0 <= k && k < s.len() as int && s[k as usize] == min(s)
    decreases s.len()
{
    if s.len() == 1 {
        proof {
            assert(min(s) == s[0]);
            assert(forall|k: int| 0 <= k && k < s.len() as int ==> min(s) <= s[k as usize]);
            assert(exists|k: int| 0 <= k && k < s.len() as int && s[k as usize] == min(s));
        }
    } else {
        // induction on tail
        min_is_min(s[1..]);
        let tail = min(s[1..]);
        proof {
            // from inductive hypothesis on tail
            assert(forall|k: int| 0 <= k && k < s[1..].len() as int ==> tail <= s[(k + 1) as usize]);
            assert(exists|k: int| 0 <= k && k < s[1..].len() as int && s[(k + 1) as usize] == tail);

            if s[0] <= tail {
                // min(s) == s[0]
                assert(min(s) == s[0]);
                // s[0] <= all tail elements (by inductive hyp tail <= s[1..]) and s[0] <= tail
                assert(forall|k: int| 0 <= k && k < s.len() as int ==> min(s) <= s[k as usize]);
                assert(exists|k: int| 0 <= k && k < s.len() as int && s[k as usize] == min(s));
            } else {
                // min(s) == tail
                assert(min(s) == tail);
                // tail <= all tail elements by inductive hyp, and tail <= s[0] (since s[0] > tail)
                assert(forall|k: int| 0 <= k && k < s.len() as int ==> min(s) <= s[k as usize]);
                // existence comes from inductive hyp (shifted by 1)
                assert(exists|k: int| 0 <= k && k < s.len() as int && s[k as usize] == min(s));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &[i32]) -> (second_smallest: i32)
    requires 
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] != s[i]
    ensures 
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] == second_smallest,
        forall|k: int| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= second_smallest
// </vc-spec>
// <vc-code>
{
    let n: usize = s.len();

    // find index of a minimal element
    let mut imin: usize = 0usize;
    let mut i: usize = 1usize;
    while i < n
        invariant imin < n
        invariant i <= n
        invariant forall|k: int| 0 <= k && k < i as int ==> s[imin] <= s[k as usize]
    {
        if s[i] < s[imin] {
            imin = i;
        }
        i += 1;
    }
    // now imin is index of some minimal element among all indices
    // prove that s[imin] == min(s@)
    proof {
        // from the loop invariant for i == n
        assert(forall|k: int| 0 <= k && k < n as int ==> s[imin] <= s[k as usize]);
        // use min_is_min to get that min(s@) <= all elements
        min_is_min(s@);
        assert(min(s@) <= s[imin]);
        // combine to get equality
        assert(s[imin] == min(s@));
    }

    // find first index different from minimal value s[imin]
    let mut sec: usize = if imin == 0 { 1 } else { 0 };
    while sec < n && s[sec] == s[imin]
        invariant sec <= n
        invariant forall|k: int| 0 <= k && k < sec as int ==> s[k as usize] == s[imin]
    {
        sec += 1;
    }

    // prove that such an index exists (from function precondition) so sec < n
    proof {
        // From the function precondition there exists some index whose value != min(s@).
        // Since s[imin] == min(s@) (proved above), that index must differ from s[imin], so sec < n.
        min_is_min(s@);
        // bring the precondition: there exist i,j with s[i]==min(s@) and s[j]!=s[i]
        assert(exists|ii: int, jj: int| 0 <= ii && ii < n as int && 0 <= jj && jj < n as int && ii != jj &&
            s[ii as usize] == min(s@) && s[jj as usize] != s[ii as usize]);
        // from that, there exists an index whose value != min(s@)
        assert(exists|k: int| 0 <= k && k < n as int && s[k as usize] != min(s@));
        // since s[imin] == min(s@), there exists k with s[k] != s[imin]
        assert(exists|k: int| 0 <= k && k < n as int && s[k as usize] != s[imin]);
        // if sec == n then the loop invariant would imply all elements equal to s[imin], contradiction
        assert(sec < n);
    }

    // now sec points to some index with s[sec] != s[imin]
    // iterate over all indices to find minimal element among those != s[imin]
    let mut j: usize = 0usize;
    while j < n
        invariant j <= n
        invariant sec < n
        invariant s[sec] != s[imin]
        invariant forall|k: int| 0 <= k && k < j as int && s[k as usize] != s[imin] ==> s[sec] <= s[k as usize]
    {
        if s[j] != s[imin] && s[j] < s[sec] {
            sec = j;
        }
        j += 1;
    }

    // after the loop, sec is index of minimal element among those not equal to s[imin]
    proof {
        // sec still different from min
        assert(s[sec] != s[imin]);
        // from the loop invariant with j == n we get the required minimality property
        assert(forall|k: int| 0 <= k && k < n as int && s[k as usize] != s[imin] ==> s[sec] <= s[k as usize]);
        // existence of required pair: imin is index of min(s@) and sec is index of second smallest
        assert(exists|ii: int, jj: int| 0 <= ii && ii < n as int && 0 <= jj && jj < n as int && ii != jj &&
            s[ii as usize] == min(s@) && s[jj as usize] == s[sec]);
    }

    s[sec]
}
// </vc-code>

fn main() {
}

}