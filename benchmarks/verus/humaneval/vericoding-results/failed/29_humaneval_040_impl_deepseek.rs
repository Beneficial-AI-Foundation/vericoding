// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_triple_sum_zero_impl(a: int, b: int, c: int)
    ensures
        a + b + c == 0 ==> (a + b) == -c && (a + c) == -b && (b + c) == -a,
{
    assert(a + b + c == 0 ==> (a + b) == -c && (a + c) == -b && (b + c) == -a);
}

proof fn lemma_i8_cast_identity(x: i8)
    ensures (x as int) as i8 == x,
{
}
// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int casting errors by using ghost conversions */
    let len = l.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
    {
        let mut j: usize = i + 1;
        while j < len
            invariant
                i < j <= len,
        {
            let mut k: usize = j + 1;
            while k < len
                invariant
                    j < k <= len,
            {
                proof {
                    let seq_l = l@.map(|idx, x: i8| x as int);
                    let a_int: int = seq_l[i];
                    let b_int: int = seq_l[j];
                    let c_int: int = seq_l[k];
                    let target: int = -(a_int + b_int);
                    if c_int == target {
                        lemma_triple_sum_zero_impl(a_int, b_int, c_int);
                        assert(a_int + b_int + c_int == 0);
                        assert(l[i] == a_int as i8);
                        assert(l[j] == b_int as i8);
                        assert(l[k] == c_int as i8);
                    }
                }
                if l[k] == -((l[i] as i16 + l[j] as i16) as i8) {
                    return true;
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>


}

fn main() {}