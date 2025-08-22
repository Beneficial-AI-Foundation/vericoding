use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
{
    if x == 0 {
        return Some(0);
    } else if x == 1 {
        return Some(0);
    } else if x == 2 {
        return Some(1);
    }

    let mut a: u32 = 0; // fibfib(0)
    let mut b: u32 = 0; // fibfib(1) 
    let mut c: u32 = 1; // fibfib(2)
    
    let mut i: u32 = 3;
    while i <= x
        invariant
            3 <= i <= x + 1,
            a == spec_fibfib((i - 3) as nat),
            b == spec_fibfib((i - 2) as nat),
            c == spec_fibfib((i - 1) as nat),
    {
        let sum_ab = match a.checked_add(b) {
            Some(s) => s,
            None => return None,
        };
        
        let new_val = match sum_ab.checked_add(c) {
            Some(s) => s,
            None => return None,
        };
        
        a = b;
        b = c;
        c = new_val;
        i = i + 1;
    }
    
    Some(c)
}

}
fn main() {}