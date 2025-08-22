use vstd::prelude::*;

verus! {
    fn triple(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        x * 3
    }

    fn triple_if(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        if x == 0 {
            0
        } else {
            x + x + x
        }
    }

    fn triple_over(x: u32) -> (r: u32)
        requires x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        let doubled = x + x;
        doubled + x
    }

    fn triple_conditions(x: u32) -> (r: u32)
        requires x % 2 == 0 && x <= 0x55555555u32,
        ensures r as int == 3 * (x as int)
    {
        let half = x / 2;
        let three_halves = half + half + half;
        three_halves * 2
    }

    fn caller() {
        let result1 = triple(10);
        let result2 = triple_if(20);
        let result3 = triple_over(30);
        let result4 = triple_conditions(40);
    }
}

fn main() {}