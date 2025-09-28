use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool 
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if sub.len() > str.len() {
        false  
    } else {
        sub == str.subrange(0, sub.len() as int) || is_substring(sub, str.subrange(1, str.len() as int))
    }
}

// We spent 2h each on this assignment

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| #![auto] 0 <= i && i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i && i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}


spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1, str2)
    //ensures !found <==> have_not_common_k_substring_pred(k, str1, str2) // This postcondition follows from the above lemma.
{
    assume(false);
    false
}

// <vc-helpers>
spec fn is_prefix_of_subrange(pre: Seq<char>, str: Seq<char>, start: int) -> bool {
    pre.len() <= (str.len() - start) && 
    pre == str.subrange(start, start + pre.len() as int)
}

proof fn lemma_is_substring_pred_iff_exists_prefix_of_subrange(sub: Seq<char>, str: Seq<char>)
    ensures is_substring_pred(sub, str) <==> (exists|i: int| #![trigger is_prefix_of_subrange(sub, str, i)] 0 <= i && i <= str.len() && is_prefix_of_subrange(sub, str, i))
{
    assert forall|i: int| 0 <= i && i <= str.len()
        implies (is_prefix_pred(sub, str.subrange(i, str.len() as int)) <==> is_prefix_of_subrange(sub, str, i)) by {
        assert(str.subrange(i, str.len() as int).len() == str.len() - i);
        assert(sub.len() <= str.len() - i <==> sub.len() <= str.subrange(i, str.len() as int).len());
        assert(sub == (str.subrange(i, str.len() as int)).subrange(0, sub.len() as int) <==> sub == str.subrange(i, i + sub.len() as int));
    }
}

proof fn lemma_have_common_k_substring_pred_iff_exists_substring(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(k, str1, str2) <==> (exists|i1: int| 0 <= i1 && (i1 as nat) + k <= str1.len() as nat && is_substring_pred(str1.subrange(i1, i1 + k as int), str2))
{
    assert forall|i1: int, j1: int| 0 <= i1 && (i1 as nat) + k <= str1.len() as nat && j1 == i1 + k
        implies (is_substring_pred(str1.subrange(i1, j1), str2) <==> is_substring_pred(str1.subrange(i1, i1 + k as int), str2)) by {}
}

proof fn lemma_have_common_k_substring_pred_iff_exists_substring_expanded(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(k, str1, str2) <==> (exists|i1: int, i2: int| #![trigger str1.subrange(i1, i1 + k as int), str2.subrange(i2, i2 + k as int)] 0 <= i1 && (i1 as nat) + k <= str1.len() as nat && 0 <= i2 && (i2 as nat) + k <= str2.len() as nat && str1.subrange(i1, i1 + k as int) == str2.subrange(i2, i2 + k as int))
{
    lemma_have_common_k_substring_pred_iff_exists_substring(k, str1, str2);
    assert forall|i1: int| 0 <= i1 && (i1 as nat) + k <= str1.len() as nat
        implies (is_substring_pred(str1.subrange(i1, i1 + k as int), str2) <==> (exists|i2: int| 0 <= i2 && (i2 as nat) + k <= str2.len() as nat && str1.subrange(i1, i1 + k as int) == str2.subrange(i2, i2 + k as int))) by {
        let sub_k = str1.subrange(i1, i1 + k as int);
        if is_substring_pred(sub_k, str2) {
            assert (exists|j: int| 0 <= j && j <= str2.len() && is_prefix_pred(sub_k, str2.subrange(j, str2.len() as int)));
            let i_prime = choose|j: int| 0 <= j && j <= str2.len() && is_prefix_pred(sub_k, str2.subrange(j, str2.len() as int));
            assert(sub_k.len() == k);
            assert(sub_k == (str2.subrange(i_prime, str2.len() as int)).subrange(0, sub_k.len() as int));
            assert(sub_k == str2.subrange(i_prime, i_prime + k as int));
            assert(0 <= i_prime && (i_prime as nat) + k <= str2.len() as nat);
        } else {
            assert forall|i2: int| 0 <= i2 && (i2 as nat) + k <= str2.len() as nat implies sub_k != str2.subrange(i2, i2 + k as int) by {
                assert (is_not_substring_pred(sub_k, str2));
                assert forall|j: int| 0 <= j && j <= str2.len() implies is_not_prefix_pred(sub_k, str2.subrange(j, str2.len() as int)) by {
                    if (sub_k.len() as int) <= str2.subrange(j,str2.len() as int).len() && sub_k == str2.subrange(j,str2.len() as int).subrange(0, sub_k.len() as int) {
                        assert(is_prefix_pred(sub_k, str2.subrange(j,str2.len() as int)));
                        assert(false);
                    }
                };
                if (0 <= i2 && (i2 as nat) + k <= str2.len() as nat) {
                    assert(k as int <= str2.len() - i2);
                    assert(sub_k != str2.subrange(i2, i2 + k as int)) by {
                        assert(is_not_prefix_pred(sub_k, str2.subrange(i2, str2.len() as int)));
                        if ((sub_k.len() as int) == (str2.subrange(i2, str2.len() as int)).len() || (sub_k.len() as int) < (str2.subrange(i2, str2.len() as int)).len()) {
                            if (sub_k == (str2.subrange(i2, str2.len() as int)).subrange(0, sub_k.len() as int)) {
                                assert(false);
                            }
                        }
                    };
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures (forall|k: nat| #![auto] len < k && k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2))
        && have_common_k_substring_pred(len as nat, str1, str2)
// </vc-spec>
// <vc-code>
{
    let n1 = str1.len();
    let n2 = str2.len();

    if n1 == 0 {
        assert(have_common_k_substring_pred(0 as nat, str1, str2));
        assert(forall|k: nat| 0 < k && k <= n1 ==> !have_common_k_substring_pred(k as nat, str1, str2)) by {
            assert forall|k_implies: nat| 0 < k_implies && k_implies <= n1 implies !have_common_k_substring_pred(k_implies, str1, str2) by {
                assert(k_implies > 0 && k_implies <= 0); // This is a contradiction, so the implication body is trivially true.
            }
        }
        return 0;
    }

    let mut low: usize = 0;
    let mut high: usize = n1;
    let mut ans: usize = 0;

    while low <= high
        invariant 0 <= low && low <= n1 + 1
        invariant 0 <= high && high <= n1
        invariant ans <= n1
        invariant (low <= high) ==> (ans <= high)
        invariant (ans <= low) || (low == n1 + 1)
        invariant (ans as nat) <= n1 as nat
        invariant (ans == 0 || have_common_k_substring_pred(ans as nat, str1, str2))
        invariant (forall|k_loop: nat| (high as nat) < k_loop && k_loop <= (n1 as nat) ==> !have_common_k_substring_pred(k_loop, str1, str2))
        invariant (forall|k_loop: nat| k_loop <= (low as nat) && (ans as nat) < k_loop ==> !have_common_k_substring_pred(k_loop, str1, str2))
    {
        let mid = low + (high - low) / 2;

        if mid == 0 {
            // have_common_k_substring will return true for k=0 by spec.
            // We can then try to find a larger common substring by moving 'low' up.
            ans = 0;
            low = mid + 1;
        } else if have_common_k_substring(mid, str1, str2) {
            ans = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    // Proof that the final `ans` satisfies the postconditions
    assert(ans <= n1);

    if ans > 0 {
        assert(have_common_k_substring_pred(ans as nat, str1, str2));
    } else {
        assert(ans == 0);
        assert(have_common_k_substring_pred(0 as nat, str1, str2)) by {
            assert(Seq::<char>::empty().len() == 0);
            assert(0 <= 0 && (0 as nat) + (0 as nat) <= str1.len() as nat);
            assert(str1.subrange(0, 0) == Seq::<char>::empty());
            assert(is_substring_pred(Seq::<char>::empty(), str2));
            assert(exists |i1:int, j1:int| 0 <= i1 && (i1 as nat) + 0 <= str1.len() as nat && j1 == i1 + 0 && is_substring_pred(str1.subrange(i1,j1), str2));
        }
    }

    assert(forall|k_post: nat| (ans as nat) < k_post && k_post <= (n1 as nat) ==> !have_common_k_substring_pred(k_post, str1, str2)) by {
        assert forall|k_post: nat| (ans as nat) < k_post && k_post <= (n1 as nat) implies !have_common_k_substring_pred(k_post, str1, str2) by {
            if (high as nat) < k_post {
                assert(!have_common_k_substring_pred(k_post, str1, str2));
            } else { 
                assert(k_post <= (high as nat));
                if k_post < (low as nat) {
                    assert((ans as nat) < k_post && k_post < (low as nat));
                    assert(!have_common_k_substring_pred(k_post, str1, str2));
                } else { // k_post == low when low > high
                    assert(k_post == (low as nat));
                    if k_post == 0 {
                         assert(!have_common_k_substring_pred(k_post, str1, str2));
                    } else {
                        // In the previous iteration, mid was k_post.
                        // Since low > high, it means `have_common_k_substring(mid, str1, str2)` was false.
                        // Or mid was 0 and we moved low. But k_post > ans >= 0, so mid cannot be 0 here if ans is already 0.
                        let mid_val = k_post;
                        let b = have_common_k_substring(mid_val as usize, str1, str2); 
                        if b { // if it returned true, ans would be mid_val or more, contradicting ans < k_post
                            if mid_val as nat > (ans as nat) {  // this must be true for k_post if we reached this code-path
                                assert(false);
                            }
                        } else { // if it returned false, then !have_common_k_substring_pred(mid_val, str1, str2)
                            assert(!have_common_k_substring_pred(k_post, str1, str2));
                        }
                    }
                }
            }
        }
    }
    ans
}
// </vc-code>

fn main() {
}

}