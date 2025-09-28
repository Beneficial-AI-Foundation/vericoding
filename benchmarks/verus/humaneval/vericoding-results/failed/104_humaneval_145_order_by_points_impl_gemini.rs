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
/* helper modified by LLM (iteration 5): [no changes] */
fn compute_digits_sum(n: i8) -> (sum: i8)
    ensures
        sum as int == digits_sum(n as int),
{
    let m = if n < 0 {
        if n == -128 { 128 } else { -(n as i32) }
    } else {
        n as i32
    };
    let ghost m_int = m as int;

    assert(m_int == if n@ < 0 { -n@ } else { n@ });

    let mut temp_m = m;
    let mut total: i32 = 0;

    while temp_m > 0
        invariant
            m_int == (if n@ < 0 { -n@ } else { n@ }),
            temp_m >= 0,
            digits_sum_pos(m_int) == total as int + digits_sum_pos(temp_m as int),
        decreases temp_m
    {
        total = total + (temp_m % 10);
        temp_m = temp_m / 10;
    }

    proof {
        assert(m_int >= 0 && m_int <= 128);
        lemma_digits_sum_pos_bound(m_int);
        assert(total as int >= 0 && total as int <= 18);
    }

    total as i8
}

/* helper modified by LLM (iteration 5): [no changes] */
proof fn lemma_digits_sum_pos_bound(n: int)
    requires 0 <= n <= 128,
    ensures 0 <= digits_sum_pos(n) <= 18,
    decreases n,
{
    if n < 10 {
        assert(digits_sum_pos(n) == n);
    } else {
        lemma_digits_sum_pos_bound(n / 10);
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
/* code modified by LLM (iteration 5): [fixed compilation error by using correct module path vstd::seq_lib::lemma_swap_permutes] */
{
    let mut result = s;
    let mut i: usize = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            result.len() == s@.len(),
            result@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i ==> digits_sum(result@[k] as int) <= digits_sum(result@[l] as int),
            forall|k: int, l: int| 0 <= k < i && i <= l < result.len() ==> digits_sum(result@[k] as int) <= digits_sum(result@[l] as int),
        decreases result.len() - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < result.len()
            invariant
                i < j <= result.len(),
                i <= min_idx < j,
                forall|k: int| i <= k < j ==> digits_sum(result@[min_idx] as int) <= digits_sum(result@[k] as int),
            decreases result.len() - j
        {
            if compute_digits_sum(result[j]) < compute_digits_sum(result[min_idx]) {
                min_idx = j;
            }
            j = j + 1;
        }

        if i != min_idx {
            result.swap(i, min_idx);
            proof {
                vstd::seq_lib::lemma_swap_permutes(old(result)@, i as int, min_idx as int);
            }
        }

        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}