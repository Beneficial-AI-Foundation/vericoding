use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): Corrected type mismatches in `add_bit_strings_spec` proof and removed the `temp_sum == (sum - Str2Int(res_seq)) / 2_nat` invariant for loop termination. */
spec fn add_bit_strings_spec(s1: Seq<char>, s2: Seq<char>) -> (s_res: Seq<char>) {
    let val1 = Str2Int(s1);
    let val2 = Str2Int(s2);
    let sum = val1 + val2;

    if sum == 0 {
        seq!['0']
    } else {
        let mut temp_sum = sum;
        let mut res_seq: Seq<char> = Seq::empty();

        while temp_sum > 0
            invariant
                temp_sum >= 0,
                res_seq.len() >= 0,
                (sum - Str2Int(res_seq)) % 2 == 0,
                Str2Int(res_seq) <= sum,
                forall |i: int| #![trigger res_seq.index(i)] 0 <= i && i < res_seq.len() ==> (res_seq.index(i) == '0' || res_seq.index(i) == '1')
            decreases temp_sum
        {
            let bit = temp_sum % 2; // This is a nat
            let char_bit = if bit == 1 { '1' } else { '0' };
            res_seq = seq![char_bit] + res_seq;
            temp_sum = temp_sum / 2;
        }
        res_seq
    }
}

proof fn proof_Str2Int_add_bit_strings(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures
        ValidBitString(add_bit_strings_spec(s1, s2)),
        Str2Int(add_bit_strings_spec(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
    let val1 = Str2Int(s1);
    let val2 = Str2Int(s2);
    let sum = val1 + val2;

    if sum == 0 {
        assert(add_bit_strings_spec(s1, s2) =~= seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else {
        let mut temp_sum = sum;
        let mut res_seq: Seq<char> = Seq::empty();
        while temp_sum > 0
            invariant
                temp_sum >= 0,
                (sum - Str2Int(res_seq)) % 2 == 0,
                Str2Int(res_seq) <= sum,
                forall |i: int| #![trigger res_seq.index(i)] 0 <= i && i < res_seq.len() ==> (res_seq.index(i) == '0' || res_seq.index(i) == '1')
            decreases temp_sum
        {
            let bit = temp_sum % 2; // This is a nat
            let char_bit = if bit == 1 { '1' } else { '0' };
            let old_res_seq = res_seq;
            let old_temp_sum = temp_sum;
            res_seq = seq![char_bit] + res_seq;
            temp_sum = temp_sum / 2;

            assert(res_seq.index(0) == char_bit);
            assert(Str2Int(seq![char_bit]) == bit);
            if old_res_seq.len() > 0 {
                assert(Str2Int(res_seq) == (2 * Str2Int(old_res_seq) + bit) as nat);
            } else {
                assert(Str2Int(res_seq) == bit);
            }
        }
        assert(Str2Int(add_bit_strings_spec(s1, s2)) == sum);
    }
}

spec fn multiply_bit_strings_spec(s1: Seq<char>, s2: Seq<char>) -> (s_res: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    decreases Str2Int(s2)
{
    if s2.len() == 0 || (s2.len() == 1 && s2.index(0) == '0') {
        seq!['0']
    } else if s2.index(s2.len() as int - 1) == '0' {
        
        let s2_shifted = s2.subrange(0, s2.len() as int - 1);
        let s_res_rec = multiply_bit_strings_spec(s1, s2_shifted);
        Str2Int_double_seq(s_res_rec);
        
        let mut s_res_double = s_res_rec + seq!['0'];
        if s_res_rec.index(0) == '0' && s_res_rec.len() == 1 {
            s_res_double = seq!['0'];
        }
        s_res_double
    } else { // s2.index(s2.len() as int - 1) == '1'
       
        let s2_minus_one = decrement_bit_string_spec(s2);
        let s_res_rec = multiply_bit_strings_spec(s1, s2_minus_one);
        proof_Str2Int_add_bit_strings(s_res_rec, s1);
        add_bit_strings_spec(s_res_rec, s1)
    }
}

proof fn proof_multiply_bit_strings(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures
        ValidBitString(multiply_bit_strings_spec(s1, s2)),
        Str2Int(multiply_bit_strings_spec(s1, s2)) == Str2Int(s1) * Str2Int(s2)
    decreases Str2Int(s2)
{
    if s2.len() == 0 || (s2.len() == 1 && s2.index(0) == '0') {
        assert(multiply_bit_strings_spec(s1, s2) =~= seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
        assert(Str2Int(s1) * Str2Int(s2) == Str2Int(s1) * 0 == 0);
    } else if s2.index(s2.len() as int - 1) == '0' {
        let s2_shifted = s2.subrange(0, s2.len() as int - 1);
        proof_multiply_bit_strings(s1, s2_shifted);
        assert(Str2Int(multiply_bit_strings_spec(s1, s2_shifted)) == Str2Int(s1) * Str2Int(s2_shifted));
        assert(Str2Int(s2) == 2 * Str2Int(s2_shifted));
        
        let s_res_rec = multiply_bit_strings_spec(s1, s2_shifted);
        Str2Int_double_seq(s_res_rec);
        
        let mut s_res_double = s_res_rec + seq!['0'];
        if s_res_rec.index(0) == '0' && s_res_rec.len() == 1 {
            s_res_double = seq!['0'];
        }

        if s_res_rec.len() == 1 && s_res_rec.index(0) == '0' {
             assert(Str2Int(s_res_double) == 0);
        } else {
          assert(Str2Int(s_res_double) == 2 * Str2Int(s_res_rec));
        }
        assert(Str2Int(multiply_bit_strings_spec(s1, s2)) == Str2Int(s1) * Str2Int(s2));

    } else { // s2.index(s2.len() as int - 1) == '1'
        let s2_minus_one = decrement_bit_string_spec(s2);
        proof_decrement_bit_string(s2);
        proof_multiply_bit_strings(s1, s2_minus_one);
        assert(Str2Int(multiply_bit_strings_spec(s1, s2_minus_one)) == Str2Int(s1) * Str2Int(s2_minus_one));
        assert(Str2Int(s2) == Str2Int(s2_minus_one) + 1);

        let s_res_rec = multiply_bit_strings_spec(s1, s2_minus_one);
        proof_Str2Int_add_bit_strings(s_res_rec, s1);
        assert(Str2Int(add_bit_strings_spec(s_res_rec, s1)) == Str2Int(s_res_rec) + Str2Int(s1));
        assert(Str2Int(multiply_bit_strings_spec(s1, s2)) == Str2Int(s1) * Str2Int(s2));
    }
}

proof fn Str2Int_double_seq(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + seq!['0']) == 2 * Str2Int(s)
{
    if s.len() == 0 {
        assert(s + seq!['0'] =~= seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
        assert(Str2Int(s) == 0);
    } else {
        assert(Str2Int(s + seq!['0']) == 2 * Str2Int(s));
    }
}

spec fn decrement_bit_string_spec(s: Seq<char>) -> Seq<char>
    requires ValidBitString(s), Str2Int(s) > 0
    decreases s.len()
{
    if s.len() == 1 {
        seq!['0']
    } else if s.index(s.len() as int - 1) == '1' {
        s.subrange(0, s.len() as int - 1) + seq!['0']
    } else { // ends in '0'
        let prefix = s.subrange(0, s.len() as int - 1);
        let decremented_prefix = decrement_bit_string_spec(prefix);
        decremented_prefix + seq!['1']
    }
}

proof fn proof_decrement_bit_string(s: Seq<char>)
    requires ValidBitString(s), Str2Int(s) > 0
    ensures
        ValidBitString(decrement_bit_string_spec(s)),
        Str2Int(decrement_bit_string_spec(s)) == Str2Int(s) - 1
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.index(0) == '1'); // since Str2Int(s) > 0
        assert(decrement_bit_string_spec(s) =~= seq!['0']);
        assert(Str2Int(seq!['0']) == Str2Int(s) - 1);
    } else if s.index(s.len() as int - 1) == '1' {
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(Str2Int(prefix + seq!['0']) == 2 * Str2Int(prefix));
        assert(Str2Int(prefix + seq!['1']) == 2 * Str2Int(prefix) + 1);
        assert(Str2Int(decrement_bit_string_spec(s)) == Str2Int(s) - 1);

    } else { // ends in '0'
        let prefix = s.subrange(0, s.len() as int - 1);
        proof_decrement_bit_string(prefix);
        assert(Str2Int(decrement_bit_string_spec(prefix)) == Str2Int(prefix) - 1);

        assert(Str2Int(decrement_bit_string_spec(s)) == Str2Int(s) - 1);

    }
    assert(Str2Int(decrement_bit_string_spec(s)) == Str2Int(s) - 1);
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Corrected indexing for sequence `res_seq` and type mismatch in loop condition. */
{
  proof_multiply_bit_strings(s1@, s2@);
  let res_seq = multiply_bit_strings_spec(s1@, s2@);
  let mut res_vec = Vec::<char>::new();
  let mut i: int = 0;
  while (i as nat) < res_seq.len()
    invariant
      0 <= i,
      i as nat <= res_seq.len(),
      res_vec.len() as nat == i as nat,
      forall |j: int| 0 <= j && j < i ==> #[trigger] res_vec.index(j) == res_seq.index(j),
      ValidBitString(res_vec@)
  {
    res_vec.push(res_seq.index(i));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}


