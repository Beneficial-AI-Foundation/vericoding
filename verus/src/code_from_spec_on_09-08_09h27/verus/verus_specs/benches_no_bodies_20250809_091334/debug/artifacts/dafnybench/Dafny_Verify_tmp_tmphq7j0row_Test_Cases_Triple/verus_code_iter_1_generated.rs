use vstd::prelude::*;

verus! {
    fn triple(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        3 * x
    }

    fn triple_if(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        if x == 0 {
            0
        } else {
            3 * x
        }
    }

    fn triple_over(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        x + x + x
    }

    fn triple_conditions(x: u32) -> (r: u32)
        requires x % 2 == 0 && x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        3 * x
    }

    fn caller() {
        let result1 = triple(100);
        let result2 = triple_if(200);
        let result3 = triple_over(300);
        let result4 = triple_conditions(400);
    }
}

fn main() {}