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

//IMPL fibfib
fn fibfib(x: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
{
    if x == 0 {
        return Some(0);
    } else if x == 1 {
        return Some(0);
    } else if x == 2 {
        return Some(1);
    }
    
    let mut a: u32 = 0;  // fibfib(0)
    let mut b: u32 = 0;  // fibfib(1)
    let mut c: u32 = 1;  // fibfib(2)
    
    let mut i: u32 = 3;
    while i <= x
        invariant
            /* code modified by LLM (iteration 2): simplified loop invariant bounds */
            3 <= i,
            i <= x + 1,
            a == spec_fibfib((i - 3) as nat),
            b == spec_fibfib((i - 2) as nat),
            c == spec_fibfib((i - 1) as nat),
            /* code modified by LLM (iteration 2): ensure no overflow when incrementing */
            i < u32::MAX,
        decreases x - i,
    {
        let next_val = match (a.checked_add(b)) {
            Some(sum_ab) => match sum_ab.checked_add(c) {
                Some(total) => total,
                None => return None,
            },
            None => return None,
        };
        
        a = b;
        b = c;
        c = next_val;
        /* code modified by LLM (iteration 2): added assertion to prove invariant maintenance */
        assert(i <= x);
        assert(i < u32::MAX);
        i = i + 1;
        /* code modified by LLM (iteration 2): assertion to help prove loop invariant after increment */
        assert(i <= x + 1);
    }
    
    Some(c)
}

}

fn main() {}