// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() as int - 1)) + 
    (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): Added executable function to check valid bit string and lemma for leading zeros */
fn check_valid_bit_string(s: &Vec<char>) -> (is_valid: bool)
    ensures
        is_valid == valid_bit_string(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> (s@[j] == '0' || s@[j] == '1'),
        decreases s.len() - i
    {
        if s[i] != '0' && s[i] != '1' {
            return false;
        }
        i = i + 1;
    }
    true
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>, k: int)
    requires
        valid_bit_string(s),
        0 <= k <= s.len(),
        forall|j: int| 0 <= j < k ==> s[j] == '0',
    ensures
        str2int(s) == str2int(s.subrange(k, s.len() as int)),
    decreases k,
{
    if k > 0 {
        assert(s[0] == '0');
        let s_tail = s.subrange(1, s.len() as int);
        assert(valid_bit_string(s_tail));
        assert(forall|j: int| 0 <= j < k - 1 ==> s_tail[j] == '0');
        lemma_str2int_leading_zeros(s_tail, k - 1);
        assert(str2int(s.subrange(0, s.len() as int - 1)) == str2int(s_tail.subrange(0, s_tail.len() as int - 1)));
        assert(str2int(s) == 2 * str2int(s.subrange(0, s.len() as int - 1)) + 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn normalize_bit_string(s: Vec<char>) -> (t: Vec<char>)
  ensures 
    valid_bit_string(t@) &&
    t@.len() > 0 &&
    (t@.len() > 1 ==> t@[0] != '0') &&
    (valid_bit_string(s@) ==> str2int(s@) == str2int(t@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): Added decreases clause to first while loop */
    if s.len() == 0 {
        let mut result = Vec::new();
        result.push('0');
        assert(valid_bit_string(result@));
        assert(result@.len() == 1);
        return result;
    }
    
    let is_valid = check_valid_bit_string(&s);
    
    let mut i: usize = 0;
    let mut start_idx: usize = 0;
    let mut found_nonzero = false;
    let mut result = Vec::new();
    
    // Find first non-zero or reach end
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            0 <= start_idx <= i,
            is_valid ==> (
                if !found_nonzero {
                    forall|j: int| 0 <= j < i ==> s@[j] == '0'
                } else {
                    start_idx < i &&
                    s@[start_idx as int] != '0' &&
                    forall|j: int| 0 <= j < start_idx ==> s@[j] == '0'
                }
            ),
            found_nonzero <==> (exists|k: int| 0 <= k < i && s@[k] != '0'),
            result@.len() == 0,
        decreases s.len() - i
    {
        if s[i] != '0' && !found_nonzero {
            found_nonzero = true;
            start_idx = i;
        }
        i = i + 1;
    }
    
    if !found_nonzero {
        // All zeros or empty
        result.push('0');
        assert(valid_bit_string(result@));
        assert(result@.len() == 1);
        if is_valid {
            proof {
                lemma_str2int_leading_zeros(s@, s@.len() as int);
            }
        }
        return result;
    }
    
    // Copy from start_idx to end
    let mut j: usize = start_idx;
    while j < s.len()
        invariant
            start_idx <= j <= s.len(),
            result@.len() == (j - start_idx) as int,
            is_valid ==> valid_bit_string(result@),
            is_valid ==> result@ == s@.subrange(start_idx as int, j as int),
            s@[start_idx as int] != '0',
            forall|k: int| 0 <= k < start_idx ==> s@[k] == '0',
        decreases s.len() - j
    {
        result.push(s[j]);
        j = j + 1;
    }
    
    assert(is_valid ==> result@ == s@.subrange(start_idx as int, s@.len() as int));
    
    if is_valid {
        proof {
            lemma_str2int_leading_zeros(s@, start_idx as int);
            assert(str2int(s@) == str2int(s@.subrange(start_idx as int, s@.len() as int)));
            assert(str2int(s@) == str2int(result@));
        }
    }
    
    assert(result@.len() > 0);
    assert(result@.len() > 1 ==> result@[0] != '0');
    result
}
// </vc-code>


}

fn main() {}