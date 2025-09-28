// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_prefix(s: Seq<int>, i: nat) -> int
    recommends i < s.len()
    decreases i
{
    if i == 0 { s[0] }
    else if s[i as int] > max_prefix(s, (i-1) as nat) { s[i as int] }
    else { max_prefix(s, (i-1) as nat) }
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { s[0] }
    else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        if s[(s.len()-1) as int] > max_seq(sub_seq) { s[(s.len()-1) as int] }
        else { max_seq(sub_seq) }
    }
}

spec fn max_expression(n: int, p: int, q: int, r: int, a: Seq<int>) -> int
    recommends n > 0 && a.len() == n
{
    let s1 = Seq::new(n as nat, |i: int| a[i] * p);
    let s2 = Seq::new(n as nat, |i: int| max_prefix(s1, i as nat) + a[i] * q);
    let s3 = Seq::new(n as nat, |i: int| max_prefix(s2, i as nat) + a[i] * r);
    max_seq(s3)
}

spec fn valid_input(n: int, a: Seq<int>) -> bool
{
    n > 0 && a.len() == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected recursive calls and return type to match external function signature */
spec fn calculate_max_prefix_s1(a: Seq<i8>, p: i8, i: nat) -> i8
    recommends i < a.len()
    decreases i
{
    if i == 0 {
        (a[0] * p)
    } else {
        let prev_max = calculate_max_prefix_s1(a, p, (i - 1) as nat);
        prev_max.max(a[i] * p)
    }
}
spec fn calculate_max_prefix_s2(a: Seq<i8>, p: i8, q: i8, i: nat) -> i8
    recommends i < a.len()
    decreases i
{
    if i == 0 {
        (calculate_max_prefix_s1(a, p, 0) + (a[0] * q))
    } else {
        let prev_max = calculate_max_prefix_s2(a, p, q, (i - 1) as nat);
        let s1_val = calculate_max_prefix_s1(a, p, i);
        prev_max.max(s1_val + (a[i] * q))
    }
}
spec fn calculate_max_seq_s3(a: Seq<i8>, p: i8, q: i8, r: i8, len: nat) -> i8
    recommends len > 0 && len <= a.len()
    decreases len
{
    if len == 1 {
        let s1_val = calculate_max_prefix_s1(a, p, 0);
        let s2_val = (s1_val + (a[0] * q));
        (s2_val + (a[0] * r))
    } else {
        let prev_max = calculate_max_seq_s3(a, p, q, r, (len - 1) as nat);
        // The values here should be calculated up to index (len - 1) effectively.
        let s2_at_len_minus_1 = calculate_max_prefix_s2(a, p, q, (len - 1) as nat);
        let s3_current_val = (s2_at_len_minus_1 + (a[(len - 1) as int] * r));
        prev_max.max(s3_current_val)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `n as nat` to `n_nat` for type consistency and added explicit type conversions to `i8` for calculations. */
{
    let n_nat = n as nat;

    let mut i: nat = 0;
    let mut max_s1_prefix: i8 = a.view_at(0).checked_mul(p).unwrap_or(i8::MIN);
    let mut max_s2_prefix: i8 = max_s1_prefix.checked_add(a.view_at(0).checked_mul(q).unwrap_or(i8::MIN)).unwrap_or(i8::MIN);
    let mut current_max_s3: i8 = max_s2_prefix.checked_add(a.view_at(0).checked_mul(r).unwrap_or(i8::MIN)).unwrap_or(i8::MIN);

    while i < n_nat
        invariant
            0 <= i,
            i <= n_nat,
            a.len() == n_nat,
            n > 0,
            i == 0 ==> max_s1_prefix == (a.view_at(0) * p) as i8,
            i == 0 ==> max_s2_prefix == ((a.view_at(0) * p) + (a.view_at(0) * q)) as i8,
            i == 0 ==> current_max_s3 == (((a.view_at(0) * p) + (a.view_at(0) * q)) + (a.view_at(0) * r)) as i8,
            i > 0 ==> 
                max_s1_prefix == calculate_max_prefix_s1(a@, p, (i - 1) as nat),
            i > 0 ==> 
                max_s2_prefix == calculate_max_prefix_s2(a@, p, q, (i - 1) as nat),
            i > 0 ==> 
                current_max_s3 == calculate_max_seq_s3(a@, p, q, r, i as nat),
            
decreases (n_nat - i)
    {
        proof {
            if i > 0 {
                assert(max_s1_prefix == calculate_max_prefix_s1(a@, p, ((i - 1) as nat)));
                assert(max_s2_prefix == calculate_max_prefix_s2(a@, p, q, ((i - 1) as nat)));
            }
        }

        if i > 0 {
            let s1_current_val: i8 = a.view_at(i).checked_mul(p).unwrap_or(i8::MIN);
            max_s1_prefix = max_s1_prefix.max(s1_current_val);

            let s2_current_val: i8 = max_s1_prefix.checked_add(a.view_at(i).checked_mul(q).unwrap_or(i8::MIN)).unwrap_or(i8::MIN);
            max_s2_prefix = max_s2_prefix.max(s2_current_val);

            let s3_current_val: i8 = max_s2_prefix.checked_add(a.view_at(i).checked_mul(r).unwrap_or(i8::MIN)).unwrap_or(i8::MIN);
            current_max_s3 = current_max_s3.max(s3_current_val);
        }

        i = i + 1;
    }
    current_max_s3
}
// </vc-code>


}

fn main() {}