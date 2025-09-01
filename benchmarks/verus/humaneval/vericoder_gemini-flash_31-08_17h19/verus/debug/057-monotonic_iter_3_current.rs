use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(not(feature = "non_auto_spec"))]
pub fn check_monotonic_ascending(l: &Vec<i32>) -> (ret: bool) {
    let mut i = 0;
    while i < l.len() - 1 {
        if l[i] > l[i+1] {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(feature = "non_auto_spec")]
pub fn check_monotonic_ascending(l: &Vec<i32>) -> (ret: bool)
    ensures ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j))
{
    let mut i: int = 0;
    let mut result: bool = true;

    while (i as nat) < l.len()
        invariant
            0 <= i,
            i as nat <= l.len(),
            result ==> (forall|k: int, m: int| 0 <= k < m < i ==> l@.index(k) <= l@.index(m)),
            !result ==> (exists|k: int, m: int| 0 <= k < m < i && l@.index(k) > l@.index(m)),
    {
        if (i as nat) < l.len() - 1 {
            if l@[i] > l@[i+1] {
                result = false;
            }
        }
        i = i + 1;
    }
    result
}


#[verifier(external_body)]
#[cfg(not(feature = "non_auto_spec"))]
pub fn check_monotonic_descending(l: &Vec<i32>) -> (ret: bool) {
    let mut i = 0;
    while i < l.len() - 1 {
        if l[i] < l[i+1] {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(feature = "non_auto_spec")]
pub fn check_monotonic_descending(l: &Vec<i32>) -> (ret: bool)
    ensures ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j))
{
    let mut i: int = 0;
    let mut result: bool = true;

    while (i as nat) < l.len()
        invariant
            0 <= i,
            i as nat <= l.len(),
            result ==> (forall|k: int, m: int| 0 <= k < m < i ==> l@.index(k) >= l@.index(m)),
            !result ==> (exists|k: int, m: int| 0 <= k < m < i && l@.index(k) < l@.index(m)),
    {
        if (i as nat) < l.len() - 1 {
            if l@[i] < l@[i+1] {
                result = false;
            }
        }    
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    if l.len() <= 1 {
        return true;
    }

    let is_ascending = check_monotonic_ascending(&l);
    let is_descending = check_monotonic_descending(&l);

    proof {
        assert(is_ascending <==> (forall|i: int, j: int| #[trigger] (0 <= i < j && j < l@.len()) ==> l@.index(i) <= l@.index(j)));
        assert(is_descending <==> (forall|i: int, j: int| #[trigger] (0 <= i < j && j < l@.len()) ==> l@.index(i) >= l@.index(j)));
    }
    
    is_ascending || is_descending
    // impl-end
}
// </vc-code>

fn main() {}
}