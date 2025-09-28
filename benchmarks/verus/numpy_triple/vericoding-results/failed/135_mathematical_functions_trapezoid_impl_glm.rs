// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn trapezoid_ghost(y: Seq<i8>, dx: i8) -> i8 {
    if y.len() == 0 {
        0
    } else if y.len() == 1 {
        0
    } else {
        (y[0] + y[1]) / 2 * dx + trapezoid_ghost(y.subrange(1, y.len() as int), dx)
    }
}

proof fn trapezoid_constant(y: Seq<i8>, dx: i8, c: i8)
    requires 
        y.len() > 0,
        forall|i: int| 0 <= i < y.len() ==> y[i] == c,
    ensures trapezoid_ghost(y, dx) == dx * (y.len() - 1) * c
{
    if y.len() == 1 {
        assert(trapezoid_ghost(y, dx) == 0);
    } else {
        trapezoid_constant(y.subrange(1, y.len() as int), dx, c);
        let y_prime = y.subrange(1, y.len() as int);
        assert(trapezoid_ghost(y, dx) == (y[0]+y[1])/2 * dx + trapezoid_ghost(y_prime, dx));
        assert(y[0] == c && y[1] == c);
        assert((y[0]+y[1])/2 == c);
        assert(trapezoid_ghost(y, dx) == c * dx + trapezoid_ghost(y_prime, dx));
        assert(trapezoid_ghost(y_prime, dx) == dx * (y_prime.len() - 1) * c);
        assert(y_prime.len() == y.len() - 1);
        assert(trapezoid_ghost(y, dx) == c * dx + dx * (y.len() - 2) * c);
        assert(trapezoid_ghost(y, dx) == dx * c * (y.len() - 1));
    }
}

proof fn trapezoid_nonnegative(y: Seq<i8>, dx: i8)
    requires 
        y.len() > 0,
        dx > 0,
        forall|i: int| 0 <= i < y.len() ==> y[i] >= 0,
    ensures trapezoid_ghost(y, dx) >= 0
{
    if y.len() == 1 {
        assert(trapezoid_ghost(y, dx) == 0 >= 0);
    } else {
        let y_prime = y.subrange(1, y.len() as int);
        trapezoid_nonnegative(y_prime, dx);
        assert(trapezoid_ghost(y, dx) == (y[0]+y[1])/2 * dx + trapezoid_ghost(y_prime, dx));
        assert(y[0] >= 0 && y[1] >= 0);
        assert((y[0]+y[1])/2 >= 0);
        assert((y[0]+y[1])/2 * dx >= 0);
        assert(trapezoid_ghost(y_prime, dx) >= 0);
        assert(trapezoid_ghost(y, dx) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i8>, dx: i8) -> (result: i8)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] == y@[0]) ==> 
            result as int == dx as int * (y.len() - 1) as int * y@[0],
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    let n = y.len();
    if n == 1 {
        0
    } else {
        let mut total: i8 = 0;
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                total == trapezoid_ghost(y@.subrange(0, i as int + 1), dx),
            decreases (n - 1) - i
        {
            let avg_height = (y[i] + y[i+1]) / 2;
            total = total + avg_height * dx;
            i = i + 1;
        }
        proof {
            let is_constant = forall|j: int| 0 <= j < y@.len() ==> y@[j] == y@[0];
            if is_constant {
                let c = y@[0];
                trapezoid_constant(y@, dx, c);
                assert(total as int == dx as int * (y@.len() - 1) as int * c as int);
            }
            let is_nonnegative = forall|j: int| 0 <= j < y@.len() ==> y@[j] >= 0;
            if is_nonnegative {
                trapezoid_nonnegative(y@, dx);
                assert(total >= 0);
            }
        }
        total
    }
}
// </vc-code>

}
fn main() {}