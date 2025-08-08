use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, PartialEq, Eq)]
enum PiecewiseFunc {
    Negate,
    Double, 
    Zero,
    Identity,
}

fn apply_func(f: PiecewiseFunc, x: i32) -> i32 {
    match f {
        PiecewiseFunc::Negate => {
            if x == i32::MIN {
                i32::MAX
            } else {
                -x
            }
        },
        PiecewiseFunc::Double => {
            if x > i32::MAX / 2 || x < i32::MIN / 2 {
                0
            } else {
                x * 2
            }
        },
        PiecewiseFunc::Zero => 0,
        PiecewiseFunc::Identity => x,
    }
}

fn check_condition(cond_id: usize, x: i32) -> bool {
    match cond_id {
        0 => x < 0,
        1 => x == 0,
        2 => x > 0,
        _ => false,
    }
}

fn piecewise(x: Vec<i32>, condlist: Vec<usize>, funclist: Vec<PiecewiseFunc>) -> (ret: Vec<i32>)
    requires
        condlist.len() == funclist.len(),
    ensures
        ret.len() == x.len(),
{
    let mut ret: Vec<i32> = Vec::new();
    
    let mut i = 0;
    while i < x.len()
        invariant
            ret.len() == i,
            i <= x.len(),
            condlist.len() == funclist.len(),
        decreases x.len() - i,
    {
        let mut value = 0;
        
        let mut j = 0;
        while j < condlist.len()
            invariant
                ret.len() == i,
                i < x.len(),
                j <= condlist.len(),
                condlist.len() == funclist.len(),
            decreases condlist.len() - j,
        {
            if check_condition(condlist[j], x[i]) {
                value = apply_func(funclist[j], x[i]);
                break;
            }
            j += 1;
        }
        
        ret.push(value);
        i += 1;
    }
    
    ret
}

}

fn main() {}