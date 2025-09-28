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
/* helper modified by LLM (iteration 3): fixed mutable borrowing issue in swap */
fn exec_digits_sum_inner(n: u32) -> (sum: u8)
    ensures sum as int == digits_sum_pos(n as int)
    decreases n
{
    if n < 10 {
        n as u8
    } else {
        let last_digit = (n % 10) as u8;
        let rest = n / 10;
        let rest_sum = exec_digits_sum_inner(rest);
        last_digit + rest_sum
    }
}

/* helper modified by LLM (iteration 3): fixed cast to avoid using int in exec code */
fn exec_digits_sum(n: i8) -> (sum: u8)
    ensures sum as int == digits_sum(n as int)
{
    let n_abs = n.abs() as u32;
    exec_digits_sum_inner(n_abs)
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
/* code modified by LLM (iteration 3): fixed mutable borrowing by using indices */
{
    let mut sorted = s;
    let n = sorted.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            sorted@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| n - i <= k < l < n ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                sorted@.to_multiset() == s@.to_multiset(),
                forall|k: int, l: int| n - i <= k < l < n ==> digits_sum(sorted@[k] as int) <= digits_sum(sorted@[l] as int),
        {
            let key_j = exec_digits_sum(sorted[j]);
            let key_j1 = exec_digits_sum(sorted[j+1]);
            if key_j > key_j1 {
                let temp = sorted[j];
                sorted.set(j, sorted[j+1]);
                sorted.set(j+1, temp);
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