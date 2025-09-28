// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): Fixed Seq indexing and nat/usize conversions */
fn shift_left(s: Seq<char>, n: usize) -> (res: Seq<char>)
  requires
    valid_bit_string(s),
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s) * pow2(n as nat),
{
    let mut zeros = Seq::<char>::empty();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            zeros.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> zeros[j] == '0',
        decreases n - i
    {
        zeros = zeros.push('0');
        i = i + 1;
    }
    let mut result = zeros;
    let mut j: usize = 0;
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            result.len() == n as nat + j,
            forall|k: int| 0 <= k < n as int ==> result[k] == '0',
            forall|k: int| n as int <= k < n as int + j as int ==> result[k] == s.index((k - n as int) as int),
        decreases s.len() - j
    {
        result = result.push(s.index(j as int));
        j = j + 1;
    }
    proof {
        assert(result.len() == n as nat + s.len());
        assert(forall|k: int| 0 <= k < n as int ==> result[k] == '0');
        assert(forall|k: int| n as int <= k < result.len() ==> result[k] == s.index((k - n as int) as int));
    }
    result
}

spec fn pow2(n: nat) -> nat
  decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed Seq indexing and nat/usize conversions */
{
    let mut result = Seq::<char>::new(1nat, |_| '0');
    let mut i: usize = 0;
    let s2_len = s2.len();
    while i < s2_len
        invariant
            0 <= i <= s2_len,
            s2_len == s2.len(),
            valid_bit_string(s2@),
            valid_bit_string(result),
            str2int(result) == str2int(s1@) * str2int(s2@.subrange(0, i as int)),
        decreases s2_len - i
    {
        if s2[i] == '1' {
            let shifted = shift_left(s1@, i);
            result = add(result, shifted);
        }
        i = i + 1;
    }
    let mut res_vec = Vec::<char>::new();
    let mut j: usize = 0;
    while j < result.len()
        invariant
            0 <= j <= result.len(),
            res_vec.len() == j,
            res_vec@.subrange(0, j as int) =~= result.subrange(0, j as int),
        decreases result.len() - j
    {
        res_vec.push(result.index(j as int));
        j = j + 1;
    }
    res_vec
}
// </vc-code>


}

fn main() {}