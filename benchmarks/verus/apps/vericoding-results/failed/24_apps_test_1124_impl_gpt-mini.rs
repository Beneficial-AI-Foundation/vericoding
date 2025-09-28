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
/* helper modified by LLM (iteration 5): convert i8 sequence to int sequence */
spec fn values_as_int(values: Seq<i8>) -> Seq<int> {
    values.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 5): gcd divides both arguments */
proof fn gcd_divides(a: int, b: int)
    requires
        a > 0 && b > 0,
    ensures
        a % gcd(a, b) == 0 && b % gcd(a, b) == 0,
    decreases
        (if a >= b { a } else { b })
{
    if a == b {
        assert(a % gcd(a, b) == 0);
        assert(b % gcd(a, b) == 0);
    } else if a > b {
        gcd_divides(a - b, b);
        assert(a % gcd(a, b) == 0);
        assert(b % gcd(a, b) == 0);
    } else {
        gcd_divides(a, b - a);
        assert(a % gcd(a, b) == 0);
        assert(b % gcd(a, b) == 0);
    }
}

/* helper modified by LLM (iteration 5): gcd_seq divides current and suffix elements */
proof fn gcd_seq_divides_suffix(values: Seq<int>, index: int, current: int)
    requires
        0 <= index <= values.len() && current > 0,
        forall|i: int| 0 <= i < values.len() ==> values@[i] > 0,
    ensures
        current % gcd_seq(values, index, current) == 0 &&
        forall|j: int| index <= j < values.len() ==> values@[j] % gcd_seq(values, index, current) == 0,
    decreases
        values.len() - index
{
    if index == values.len() {
        assert(current % gcd_seq(values, index, current) == 0);
    } else {
        let next_acc: int = gcd(current, values@[index]);
        gcd_seq_divides_suffix(values, index + 1, next_acc);
        gcd_divides(current, values@[index]);
        assert(current % gcd_seq(values, index, current) == 0);
        assert(values@[index] % gcd_seq(values, index, current) == 0);
    }
}

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
    /* code modified by LLM (iteration 5): use tracked ghost vars for spec-level ints and runtime mirrors for loops, synchronizing updates */
    let s: Seq<int> = values_as_int(values@);
    let n_usize: usize = values.len();
    let tracked mut n: int = s.len();

    let mut i_r: usize = 1;
    let tracked mut i: int = 1;

    let mut cur_r: i64 = s@[0] as i64;
    let tracked mut cur: int = s@[0];

    while i_r < n_usize
        invariant
            0 <= i && i <= n,
            cur > 0,
            gcd_seq(s, i, cur) == gcd_of_all(s),
        decreases
            n - i
    {
        let v_r: i64 = values[i_r] as i64;
        let tracked v: int = s@[i];

        let mut a_r: i64 = cur_r;
        let mut b_r: i64 = v_r;
        let tracked mut a: int = cur;
        let tracked mut b: int = v;

        while a_r != b_r
            invariant
                a_r > 0 && b_r > 0,
                a > 0 && b > 0,
                a_r as int == a,
                b_r as int == b,
            decreases
                (if a >= b { a } else { b })
        {
            if a_r > b_r {
                a_r = a_r - b_r;
                a = a - b;
            } else {
                b_r = b_r - a_r;
                b = b - a;
            }
        }

        let new_cur_r: i64 = a_r;
        let new_cur: int = a;

        proof {
            assert(new_cur == gcd(cur, v));
        }

        cur_r = new_cur_r;
        cur = new_cur;

        i_r = i_r + 1;
        i = i + 1;
    }

    proof {
        assert(i == n);
        assert(cur == gcd_seq(s, n, cur));
        assert(cur == gcd_of_all(s));
    }

    let result: i8 = cur as i8;
    result
}

// </vc-code>


}

fn main() {}