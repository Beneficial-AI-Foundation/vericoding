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

/* code modified by LLM (iteration 4): Fixed function syntax by properly placing ensures clause before opening brace and removed incorrect return statement */
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
            3 <= i <= x + 1,
            a == spec_fibfib((i - 3) as nat),
            b == spec_fibfib((i - 2) as nat),
            c == spec_fibfib((i - 1) as nat),
            i <= x + 1,
        decreases x - i,
    {
        let temp_sum = a.checked_add(b);
        if temp_sum.is_none() {
            return None;
        }
        let new_val = temp_sum.unwrap().checked_add(c);
        if new_val.is_none() {
            return None;
        }
        
        a = b;
        b = c;
        c = new_val.unwrap();
        i = i + 1;
    }
    
    Some(c)
}

}
fn main() {}