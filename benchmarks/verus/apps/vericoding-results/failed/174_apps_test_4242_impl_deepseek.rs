// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn common_divisors(a: int, b: int) -> Set<int>
{
  Set::new(|d: int| 1 <= d <= a && a % d == 0 && b % d == 0)
}

spec fn valid_input(a: int, b: int, k: int) -> bool
{
  a > 0 && b > 0 && k >= 1 && common_divisors(a, b).len() >= k
}

spec fn is_kth_largest_common_divisor(a: int, b: int, k: int, result: int) -> bool
{
  valid_input(a, b, k) ==> (
    result > 0 &&
    a % result == 0 && b % result == 0 &&
    common_divisors(a, b).contains(result) &&
    Set::new(|d: int| common_divisors(a, b).contains(d) && d > result).len() == (k - 1)
  )
}
// </vc-preamble>

// <vc-helpers>
predicate non_empty_common_divisors!(a: int, b: int) -> bool {
    common_divisors(a, b).len() >= 1
}

spec fn common_divisors_sorted(a: int, b: int) -> Seq<int>
    recommends a > 0 && b > 0
{
    let divisors = common_divisors(a, b);
    let mut seq = Seq::<int>::empty();
    
    let mut d = a;
    while d >= 1
        invariant
            d >= 0,
            forall|i: int| d < i <= a ==> divisors.contains(i) ==> seq.contains(i),
            forall|val: int| seq.contains(val) ==> divisors.contains(val),
            seq.is_sorted(),
        decreases d
    {
        if divisors.contains(d) {
            seq = seq.insert(0, d);
        }
        d -= 1;
    }
    seq
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error and iterates from largest to smallest */
    let ai = a as int;
    let bi = b as int;
    let ki = k as int;
    
    let mut count = 0;
    let mut d = a;
    
    while d >= 1
        invariant
            d >= 0,
            count >= 0,
            count <= common_divisors(ai, bi).len(),
        decreases d
    {
        if ai % (d as int) == 0 && bi % (d as int) == 0 {
            count += 1;
            if count == ki {
                return d;
            }
        }
        d -= 1;
    }
    
    assert(false);
    0
}
// </vc-code>


}

fn main() {}