// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digits_sum_pos(n: int) -> int
  decreases n
{
  if n >= 0 {
    if n < 10 { n } else { digits_sum_pos(n / 10) + n % 10 }
  } else {
    0
  }
}

spec fn digits_sum(n: int) -> int {
  if n < 0 { digits_sum_pos(-n) } else { digits_sum_pos(n) }
}
// </vc-preamble>

// <vc-helpers>

spec fn cmp_local(a: int, b: int) -> bool {
    digits_sum(a) <= digits_sum(b)
}

spec fn is_sorted_by(s: Seq<i8>, f: spec_fn(int, int) -> bool) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> f(s[i] as int, s[j] as int)
}

spec fn same_elements(a: Seq<i8>, b: Seq<i8>) -> bool {
    a.to_multiset() == b.to_multiset()
}

/* helper modified by LLM (iteration 5): Add type safety and conversion helpers */
fn usize_from_int(n: int) -> (result: usize)
    requires 0 <= n < 0xffffffffffffffff
    ensures result == n as usize
{
    if n == 0 {
        0
    } else {
        let prev = usize_from_int(n - 1);
        prev + 1
    }
}
// </vc-helpers>

// <vc-spec>
fn order_by_points(s: Vec<i8>) -> (sorted: Vec<i8>)
  ensures 
      forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> digits_sum(sorted@[i] as int) <= digits_sum(sorted@[j] as int),
      sorted@.len() == s@.len(),
      s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix type conversion and loop logic */
    let mut sorted = s.clone();
    let mut i: int = 0;
    while i < sorted.len() as int
        invariant
            0 <= i <= sorted@.len() as int,
            sorted@.len() == s@.len(),
            sorted@.to_multiset() == s@.to_multiset()
    {
        let mut j: int = 0;
        while j < sorted.len() as int - i - 1
            invariant
                0 <= j <= sorted@.len() as int - i - 1,
                sorted@.len() == s@.len(),
                sorted@.to_multiset() == s@.to_multiset()
        {
            let a = sorted[j as usize];
            let b = sorted[(j + 1) as usize];
            proof {
                let a_sum = digits_sum(a as int);
                let b_sum = digits_sum(b as int);
            }
            if digits_sum(a as int) > digits_sum(b as int) {
                sorted.swap(j as usize, (j + 1) as usize);
            }
            j += 1;
        }
        i += 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}