use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn set_filter_count<T>(s: Set<T>, f: spec_fn(T) -> bool) -> nat
    decreases s.len(),
{
    if s.finite() {
        if s.is_empty() {
            0
        } else {
            let x = s.choose();
            let remaining = s.remove(x);
            let count_remaining = set_filter_count(remaining, f);
            if f(x) {
                count_remaining + 1
            } else {
                count_remaining
            }
        }
    } else {
        0
    }
}

proof fn set_filter_count_properties<T>(s: Set<T>, f: spec_fn(T) -> bool)
    ensures
        set_filter_count(s, f) == s.filter(f).len(),
    decreases s.len(),
{
    if s.finite() {
        if s.is_empty() {
        } else {
            let x = s.choose();
            let remaining = s.remove(x);
            set_filter_count_properties(remaining, f);
        }
    }
}

spec fn set_to_vec<T>(s: Set<T>) -> Vec<T>
    recommends s.finite(),
    decreases s.len(),
{
    if s.is_empty() {
        Vec::<T>::new()
    } else {
        let x = s.choose();
        let remaining = s.remove(x);
        let mut vec = set_to_vec(remaining);
        vec.push(x);
        vec
    }
}

proof fn set_to_vec_properties<T>(s: Set<T>)
    ensures
        s.finite() ==> set_to_vec(s)@.to_set() == s,
    decreases s.len(),
{
    if s.finite() && !s.is_empty() {
        let x = s.choose();
        let remaining = s.remove(x);
        set_to_vec_properties(remaining);
    }
}

spec fn set_iter_count<T>(s: Set<T>, f: spec_fn(T) -> bool) -> nat
    decreases s.len(),
{
    if s.finite() {
        if s.is_empty() {
            0
        } else {
            let x = s.choose();
            let remaining = s.remove(x);
            let count_remaining = set_iter_count(remaining, f);
            if f(x) {
                count_remaining + 1
            } else {
                count_remaining
            }
        }
    } else {
        0
    }
}

proof fn set_iter_count_properties<T>(s: Set<T>, f: spec_fn(T) -> bool)
    ensures
        set_iter_count(s, f) == s.filter(f).len(),
    decreases s.len(),
{
    if s.finite() {
        if s.is_empty() {
        } else {
            let x = s.choose();
            let remaining = s.remove(x);
            set_iter_count_properties(remaining, f);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut remaining = numbers;
    let old_remaining = remaining;
    
    proof {
        set_iter_count_properties(remaining, |i: int| i < threshold);
    }
    
    while !remaining.is_empty()
        invariant
            remaining.finite(),
            count + set_iter_count(remaining, |i: int| i < threshold) == old_remaining.filter(|i: int| i < threshold).len(),
            remaining.subset_of(numbers),
    {
        let x = remaining.choose();
        remaining = remaining.remove(x);
        if x < threshold {
            count = count + 1;
        }
        
        proof {
            set_iter_count_properties(remaining, |i: int| i < threshold);
        }
    }
    count
}
// </vc-code>

fn main() {}

}