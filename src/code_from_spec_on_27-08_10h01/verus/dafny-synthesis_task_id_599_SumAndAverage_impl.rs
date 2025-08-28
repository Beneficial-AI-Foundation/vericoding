use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sum_formula(n: i32) -> int {
    (n as int) * ((n as int) + 1) / 2
}

proof fn sum_formula_correct(n: i32)
    requires n > 0
    ensures sum_formula(n) == (n as int) * ((n as int) + 1) / 2
{
}

proof fn arithmetic_bounds(n: i32)
    requires n > 0 && n <= 46340
    ensures (n as int) * ((n as int) + 1) / 2 <= 0x7fffffff
{
    let n_int = n as int;
    assert(n_int <= 46340);
    assert(n_int + 1 <= 46341);
    assert(n_int * (n_int + 1) <= 46340 * 46341);
    assert(46340 * 46341 == 2147395140);
    assert(2147395140 / 2 == 1073697570);
    assert(1073697570 <= 0x7fffffff);
}

proof fn sum_divisible_by_n(n: i32)
    requires n > 0
    ensures (n as int) * ((n as int) + 1) / 2 % (n as int) == 0
{
    let n_int = n as int;
    if n_int % 2 == 0 {
        assert(n_int * (n_int + 1) % (2 * n_int) == 0);
    } else {
        assert((n_int + 1) % 2 == 0);
        assert(n_int * (n_int + 1) % (2 * n_int) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_and_average(n: i32) -> (res: (i32, i32))
    requires n > 0
    ensures res.0 == n * (n + 1) / 2 && res.1 * n == res.0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let sum = n * (n + 1) / 2;
    let average = sum / n;
    
    proof {
        let sum_int = (n as int) * ((n as int) + 1) / 2;
        arithmetic_bounds(n);
        assert(sum_int <= 0x7fffffff);
        sum_divisible_by_n(n);
        assert(sum_int % (n as int) == 0);
        assert(sum == sum_int);
        assert(average * n == sum);
    }
    
    (sum, average)
}
// </vc-code>

fn main() {}

}