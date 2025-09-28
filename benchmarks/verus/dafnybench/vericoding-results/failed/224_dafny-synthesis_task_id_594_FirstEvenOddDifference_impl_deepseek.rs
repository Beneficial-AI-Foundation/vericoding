use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
spec fn min_even_index(a: Seq<int>) -> int
    recommends a.len() > 0
{
    choose|i: int| 
        0 <= i < a.len() && 
        is_even(a[i]) && 
        (forall|k: int| 0 <= k < i ==> is_odd(a[k]))
}

spec fn min_odd_index(a: Seq<int>) -> int
    recommends a.len() > 0
{
    choose|j: int| 
        0 <= j < a.len() && 
        is_odd(a[j]) && 
        (forall|k: int| 0 <= k < j ==> is_even(a[k]))
}

proof fn min_even_exists(a: Seq<int>)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i]),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i])
    ensures 
        exists|i: int| 
            0 <= i < a.len() && 
            is_even(a[i]) && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k]))
{
    let first_even = choose|i: int| 0 <= i < a.len() && is_even(a[i]);
    let mut min_index = first_even;
    let mut found = false;
    
    while !found
        invariant 
            min_index >= 0 && min_index < a.len(),
            is_even(a[min_index]),
            forall|k: int| 0 <= k < min_index ==> !is_even(a[k])
    {
        let prev = min_index - 1;
        if prev >= 0 && is_even(a[prev]) {
            min_index = prev;
        } else {
            found = true;
        }
    }
}

proof fn min_odd_exists(a: Seq<int>)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i]),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i])
    ensures 
        exists|j: int| 
            0 <= j < a.len() && 
            is_odd(a[j]) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k]))
{
    let first_odd = choose|j: int| 0 <= j < a.len() && is_odd(a[j]);
    let mut min_index = first_odd;
    let mut found = false;
    
    while !found
        invariant 
            min_index >= 0 && min_index < a.len(),
            is_odd(a[min_index]),
            forall|k: int| 0 <= k < min_index ==> !is_odd(a[k])
    {
        let prev = min_index - 1;
        if prev >= 0 && is_odd(a[prev]) {
            min_index = prev;
        } else {
            found = true;
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &[i32]) -> (diff: i32)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 
            0 <= j < a.len() && 
            is_even(a[i] as int) && 
            is_odd(a[j] as int) && 
            diff == a[i] - a[j] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k] as int)) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k] as int))
// </vc-spec>
// <vc-code>
{
    proof {
        min_even_exists(a@.map(|x| x as int));
        min_odd_exists(a@.map(|x| x as int));
    }
    
    let mut first_even_idx = 0;
    let mut first_odd_idx = 0;
    let mut found_even = false;
    let mut found_odd = false;
    
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            !found_even ==> forall|k: int| 0 <= k < i ==> is_odd(a@[k] as int),
            found_even ==> (
                0 <= first_even_idx < a.len() && 
                is_even(a@[first_even_idx] as int) && 
                forall|k: int| 0 <= k < first_even_idx ==> is_odd(a@[k] as int)
            ),
            !found_odd ==> forall|k: int| 0 <= k < i ==> is_even(a@[k] as int),
            found_odd ==> (
                0 <= first_odd_idx < a.len() && 
                is_odd(a@[first_odd_idx] as int) && 
                forall|k: int| 0 <= k < first_odd_idx ==> is_even(a@[k] as int)
            )
        decreases a.len() - i
    {
        let current = a[i];
        if !found_even && current % 2 == 0 {
            first_even_idx = i;
            found_even = true;
        }
        if !found_odd && current % 2 != 0 {
            first_odd_idx = i;
            found_odd = true;
        }
        i += 1;
    }
    
    a[first_even_idx] - a[first_odd_idx]
}
// </vc-code>

fn main() {
}

}