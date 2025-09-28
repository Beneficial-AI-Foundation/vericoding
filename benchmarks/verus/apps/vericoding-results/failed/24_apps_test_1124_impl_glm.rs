// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(values: Seq<int>) -> bool {
    values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
}

spec fn gcd(a: int, b: int) -> int
    decreases (if a >= b { a } else { b }) when a > 0 && b > 0
{
    if a > 0 && b > 0 {
        if a == b {
            a
        } else if a > b {
            gcd(a - b, b)
        } else {
            gcd(a, b - a)
        }
    } else {
        1
    }
}

spec fn gcd_seq(values: Seq<int>, index: int, current: int) -> int
    decreases values.len() - index when 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
{
    if 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        if index == values.len() {
            current
        } else {
            gcd_seq(values, index + 1, gcd(current, values[index as int]))
        }
    } else {
        1
    }
}

spec fn gcd_of_all(values: Seq<int>) -> int {
    if values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        gcd_seq(values, 1, values[0])
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn values_as_int(values: Seq<i8>) -> Seq<int> {
    values.map(|i, x| x as int)
}

fn exec_gcd(a: i8, b: i8) -> (result: i8)
    requires a > 0 && b > 0
    ensures 
        result > 0,
        (a as int) % (result as int) == 0,
        (b as int) % (result as int) == 0,
        forall|k: int| 
            (#[trigger] (a as int) % k == 0) && 
            (#[trigger] (b as int) % k == 0) 
            ==> k <= result as int
{
    let mut result = 1;
    let mut i = 1;
    while i <= a && i <= b
        invariant 
            1 <= i <= a+1 && 1 <= i <= b+1,
            result > 0,
            (a as int) % (result as int) == 0,
            (b as int) % (result as int) == 0,
            forall|k: int| k <= i && (a as int) % k == 0 && (b as int) % k == 0 ==> k <= result as int
        decreases (a+1-i) + (b+1-i)
    {
        if a % i == 0 && b % i == 0 {
            result = i;
        }
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): added trigger annotations to quantifier in exec_gcd postcondition */
// </vc-helpers>

// <vc-spec>
fn solve(values: Vec<i8>) -> (result: i8)
    requires valid_input(values_as_int(values@)) && values.len() <= 127
    ensures 
        result > 0 &&
        result as int == gcd_of_all(values_as_int(values@)) &&
        forall|i: int| 0 <= i < values@.len() ==> (values@[i] as int) % (result as int) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): corrected values.len() - 1 to nat type */
    let mut current = values[0];
    let mut index = 1;
    while index < values.len()
        invariant 
            1 <= index <= values.len(),
            current > 0,
            forall|i: int| 0 <= i < index ==> (values_as_int(values@)[i] as int) % (current as int) == 0,
            forall|k: int| k > 0 && 
                (forall|i: int| 0 <= i < index ==> values_as_int(values@)[i] % k == 0) 
                ==> k <= current as int
        decreases values.len() - index
    {
        let next = values[index];
        let new_current = exec_gcd(current, next);
        current = new_current;
        index += 1;
    }

    proof {
        let values_seq = values_as_int(values@);
        assert(forall|i: int| 0 <= i < values_seq.len() ==> values_seq[i] % (current as int) == 0);
    }
    current
}
// </vc-code>


}

fn main() {}