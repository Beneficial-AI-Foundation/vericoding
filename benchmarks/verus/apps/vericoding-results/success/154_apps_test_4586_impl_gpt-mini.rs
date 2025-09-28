// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1000 <= n <= 9999
}

spec fn extract_digits(n: int) -> (int, int, int, int) {
    let d1 = n / 1000;
    let d2 = (n / 100) % 10;
    let d3 = (n / 10) % 10;
    let d4 = n % 10;
    (d1, d2, d3, d4)
}

spec fn is_good(n: int) -> bool {
    let (d1, d2, d3, d4) = extract_digits(n);
    (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): relate extract_digits spec to arithmetic */
proof fn extract_digits_ok(n: int)
    requires
        valid_input(n),
    ensures
        extract_digits(n) == (n / 1000, (n / 100) % 10, (n / 10) % 10, n % 10),
{
    reveal(extract_digits);
}

/* helper modified by LLM (iteration 4): unfold is_good to arithmetic on n */
proof fn is_good_unfold(n: int)
    requires
        valid_input(n),
    ensures
        is_good(n) <==> ((n / 1000 == (n / 100) % 10 && (n / 100) % 10 == (n / 10) % 10) || ((n / 100) % 10 == (n / 10) % 10 && (n / 10) % 10 == n % 10)),
{
    reveal(is_good);
    reveal(extract_digits);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: bool)
    requires 
        valid_input(n as int),
    ensures 
        result <==> is_good(n as int),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): compute digits using runtime integers and prove equivalence to spec using ghost ints */
    let n32: i32 = n as i32;
    let d1: i32 = n32 / 1000;
    let d2: i32 = (n32 / 100) % 10;
    let d3: i32 = (n32 / 10) % 10;
    let d4: i32 = n32 % 10;
    let res: bool = (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4);
    proof {
        let n_int: int = n as int;
        extract_digits_ok(n_int);
        is_good_unfold(n_int);
        let d1_spec: int = n_int / 1000;
        let d2_spec: int = (n_int / 100) % 10;
        let d3_spec: int = (n_int / 10) % 10;
        let d4_spec: int = n_int % 10;
        assert(d1 as int == d1_spec);
        assert(d2 as int == d2_spec);
        assert(d3 as int == d3_spec);
        assert(d4 as int == d4_spec);
        assert(res <==> is_good(n_int));
    }
    res
}

// </vc-code>


}

fn main() {}