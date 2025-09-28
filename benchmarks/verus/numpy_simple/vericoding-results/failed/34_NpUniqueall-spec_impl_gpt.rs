// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn occurs(s: Seq<i8>, x: i8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == x
}

pub proof fn unique_push_not_in(s: Seq<i8>, x: i8)
    requires
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < i ==> s[i] != s[j],
        !exists|i: int| 0 <= i < s.len() && s[i] == x,
    ensures
        forall|i: int, j: int| 0 <= i < s.len() + 1 && 0 <= j < i ==> s.push(x)[i] != s.push(x)[j],
{
    assert forall|i: int, j: int|
        0 <= i < s.len() + 1 && 0 <= j < i implies s.push(x)[i] != s.push(x)[j]
    by {
        if i < s.len() {
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == s[j]);
            assert(s[i] != s[j]);
        } else {
            assert(i == s.len());
            assert(0 <= j < s.len());
            assert(s.push(x)[i] == x);
            assert(s.push(x)[j] == s[j]);
            assert(s[j] != x);
        }
    }
}

/* helper modified by LLM (iteration 3): fix mismatched parens and decreases */
pub fn contains(v: &Vec<i8>, x: i8) -> (b: bool)
    ensures
        b == occurs(v@, x),
{
    let mut idx: usize = 0;
    let mut found: bool = false;
    while idx < v.len()
        invariant
            0 <= idx as int <= v.len() as int,
            found ==> exists|j: int| 0 <= j < idx as int && v@[j] == x,
            !found ==> forall|j: int| 0 <= j < idx as int ==> v@[j] != x,
        decreases v.len() as int - idx as int
    {
        let y = v[idx];
        if y == x {
            found = true;
        }
        idx = idx + 1;
    }
    proof {
        assert(idx as int >= v.len() as int);
        assert(idx as int <= v.len() as int);
        assert(idx as int == v.len() as int);
        if found {
            assert(exists|j: int| 0 <= j < idx as int && v@[j] == x);
            assert(occurs(v@, x));
        } else {
            assert(forall|j: int| 0 <= j < idx as int ==> v@[j] != x);
            assert(!exists|j: int| 0 <= j < idx as int && v@[j] == x);
            assert(!occurs(v@, x));
        }
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix parentheses and decreases, preserve invariants using saved old facts */
    let mut ret: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < arr.len()
        invariant
            0 <= k as int <= arr.len() as int,
            ret@.len() <= k as int,
            forall|i: int| 0 <= i < k as int ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i],
            forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
        decreases arr.len() as int - k as int
    {
        let a: i8 = arr[k];
        let present = contains(&ret, a);
        if !present {
            let ghost old = ret@;
            proof {
                // capture membership for prefix in terms of 'old'
                assert forall|i: int|
                    0 <= i < k as int implies exists|j: int| 0 <= j < old.len() && old[j] == arr@[i]
                by {
                    assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]);
                    assert(ret@ == old);
                    let j1 = choose|j1: int| 0 <= j1 < ret@.len() && ret@[j1] == arr@[i];
                    assert(0 <= j1 < old.len());
                    assert(old[j1] == arr@[i]);
                }
                assert(ret@ == old);
                assert(present == occurs(ret@, a));
                assert(present == occurs(old, a));
                assert(!occurs(old, a));
            }
            ret.push(a);
            proof {
                unique_push_not_in(old, a);
                assert(ret@ == old.push(a));
            }
            proof {
                assert forall|i: int|
                    0 <= i < k as int implies exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]
                by {
                    assert(exists|j: int| 0 <= j < old.len() && old[j] == arr@[i]);
                    let j0 = choose|j0: int| 0 <= j0 < old.len() && old[j0] == arr@[i];
                    assert(0 <= j0 < old.len());
                    assert(0 <= j0 < ret@.len());
                    assert(ret@ == old.push(a));
                    assert(ret@[j0] == old[j0]);
                    assert(ret@[j0] == arr@[i]);
                }
            }
            proof {
                assert forall|i: int|
                    0 <= i < k as int + 1 implies exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]
                by {
                    if i < k as int {
                        assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]);
                    } else {
                        assert(i == k as int);
                        let len_now = ret@.len();
                        assert(0 < len_now);
                        assert(0 <= len_now - 1 < len_now);
                        assert(arr@[k as int] == a);
                        assert(ret@[len_now - 1] == a);
                        assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[k as int]);
                    }
                }
                assert(old.len() <= k as int);
                assert(ret@.len() == old.len() + 1);
                assert(ret@.len() <= k as int + 1);
            }
        } else {
            proof {
                assert(occurs(ret@, a));
                assert forall|i: int|
                    0 <= i < k as int + 1 implies exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]
                by {
                    if i < k as int {
                        assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[i]);
                    } else {
                        assert(i == k as int);
                        assert(arr@[k as int] == a);
                        assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == a);
                        assert(exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[k as int]);
                    }
                }
                assert(ret@.len() <= k as int);
                assert(ret@.len() <= k as int + 1);
            }
        }
        k = k + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}