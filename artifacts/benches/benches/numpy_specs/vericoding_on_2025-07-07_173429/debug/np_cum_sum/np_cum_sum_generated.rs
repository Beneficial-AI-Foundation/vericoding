use vstd::prelude::*;

verus! {

fn cum_sum(a: &[i32]) -> (res: Vec<i32>)
    ensures 
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i as int] == res[i - 1] + a[i as int],
{
    let mut res = Vec::with_capacity(a.len());
    
    if a.len() > 0 {
        res.push(a[0]);
        
        let mut i: usize = 1;
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                res.len() == i,
                res.len() > 0,
                res[0] == a[0],
                forall|j: int| 1 <= j < i ==> res[j as int] == res[j - 1] + a[j as int],
            decreases a.len() - i,
        {
            let prev_val = res[i-1];
            assume(prev_val as int + a[i as int] as int >= i32::MIN as int);
            assume(prev_val as int + a[i as int] as int <= i32::MAX as int);
            res.push(prev_val + a[i]);
            assert(res[i as int] == res[i - 1] + a[i as int]);
            i = i + 1;
        }
    }
    
    res
}

}

fn main() {}