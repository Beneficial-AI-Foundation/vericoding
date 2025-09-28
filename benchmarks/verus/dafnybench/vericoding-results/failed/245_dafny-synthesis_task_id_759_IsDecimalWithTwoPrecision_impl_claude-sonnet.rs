use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_decimal_position_unique(s: &str, i: int, j: int)
    requires
        0 <= i < s@.len(),
        0 <= j < s@.len(),
        s@[i] == '.',
        s@[j] == '.',
        s@.len() - i - 1 == 2,
        s@.len() - j - 1 == 2,
    ensures
        i == j,
{
    assert(s@.len() - i - 1 == s@.len() - j - 1);
    assert(i == j);
}

proof fn lemma_no_decimal_means_no_exists(s: &str, found_decimal: bool, decimal_pos: int)
    requires
        !found_decimal,
        forall|k: int| 0 <= k < s@.len() ==> s@[k] != '.',
    ensures
        !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
{
}

proof fn lemma_wrong_precision_means_no_match(s: &str, decimal_pos: int)
    requires
        0 <= decimal_pos < s@.len(),
        s@[decimal_pos] == '.',
        s@.len() - decimal_pos - 1 != 2,
    ensures
        !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
{
    if exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2 {
        let witness_i = choose|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2;
        lemma_decimal_position_unique(s, decimal_pos, witness_i);
        assert(decimal_pos == witness_i);
        assert(s@.len() - decimal_pos - 1 == 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let mut found_decimal = false;
    let mut decimal_pos: usize = 0;
    let mut i: usize = 0;
    let len = s.len();
    
    while i < len
        invariant
            0 <= i <= len,
            len == s@.len(),
            found_decimal ==> (0 <= decimal_pos < s@.len() && s@[decimal_pos as int] == '.'),
            found_decimal ==> (forall|k: int| 0 <= k < i && k != decimal_pos ==> s@[k] != '.'),
            !found_decimal ==> (forall|k: int| 0 <= k < i ==> s@[k] != '.'),
    {
        if s.as_bytes()[i] == 46u8 {
            if found_decimal {
                proof {
                    lemma_no_decimal_means_no_exists(s, false, 0);
                }
                return false;
            }
            found_decimal = true;
            decimal_pos = i;
        }
        i += 1;
    }
    
    if !found_decimal {
        proof {
            lemma_no_decimal_means_no_exists(s, found_decimal, 0);
        }
        return false;
    }
    
    let result = (s.len() - decimal_pos - 1) == 2;
    
    proof {
        if result {
            assert(s@.len() - decimal_pos as int - 1 == 2);
            assert(exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2);
        } else {
            lemma_wrong_precision_means_no_match(s, decimal_pos as int);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}