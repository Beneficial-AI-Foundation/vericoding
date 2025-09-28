use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
proof fn even_odd_properties()
    ensures 
        forall|n: int| is_even(n) <==> n % 2 == 0,
        forall|n: int| is_odd(n) <==> n % 2 != 0,
        forall|n: int| is_even(n) ==> !is_odd(n),
        forall|n: int| is_odd(n) ==> !is_even(n),
{}

proof fn modulo_properties()
    ensures
        forall|n: int| n % 2 == 0 || n % 2 == 1,
        forall|n: int| (n % 2 == 0) <==> (n % 2 != 1),
        forall|n: int| (n % 2 == 1) <==> (n % 2 != 0),
{}

spec fn exec_is_even(n: i32) -> bool {
    is_even(n as int)
}

spec fn exec_is_odd(n: i32) -> bool {
    is_odd(n as int)
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
    let mut first_even_idx: Option<usize> = None;
    let mut first_odd_idx: Option<usize> = None;
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            first_even_idx.is_some() ==> {
                let idx = first_even_idx.unwrap();
                idx < i && idx < a.len() && is_even(a@[idx as int] as int) &&
                forall|k: int| 0 <= k < idx ==> is_odd(a@[k] as int)
            },
            first_odd_idx.is_some() ==> {
                let idx = first_odd_idx.unwrap();
                idx < i && idx < a.len() && is_odd(a@[idx as int] as int) &&
                forall|k: int| 0 <= k < idx ==> is_even(a@[k] as int)
            },
            first_even_idx.is_none() ==> forall|k: int| 0 <= k < i ==> is_odd(a@[k] as int),
            first_odd_idx.is_none() ==> forall|k: int| 0 <= k < i ==> is_even(a@[k] as int),
    {
        let element_val = a[i];
        
        if exec_is_even(element_val) && first_even_idx.is_none() {
            first_even_idx = Some(i);
        }
        if exec_is_odd(element_val) && first_odd_idx.is_none() {
            first_odd_idx = Some(i);
        }
        
        if first_even_idx.is_some() && first_odd_idx.is_some() {
            break;
        }
        
        i += 1;
    }
    
    proof {
        even_odd_properties();
        modulo_properties();
    }
    
    let even_idx = first_even_idx.unwrap();
    let odd_idx = first_odd_idx.unwrap();
    
    a[even_idx] - a[odd_idx]
}
// </vc-code>

fn main() {
}

}