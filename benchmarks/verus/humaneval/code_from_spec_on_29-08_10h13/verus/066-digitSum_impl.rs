use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn count_uppercase_sum(seq: Seq<char>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn count_uppercase_sum_empty()
    ensures count_uppercase_sum(Seq::<char>::empty()) == 0
{
}

proof fn count_uppercase_sum_append(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 }
{
    if seq.len() == 0 {
        assert(seq.push(c).drop_last() =~= seq);
        assert(seq.push(c).last() == c);
    } else {
        assert(seq.push(c).drop_last() =~= seq);
        assert(seq.push(c).last() == c);
    }
}

proof fn count_uppercase_sum_prefix(seq: Seq<char>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_uppercase_sum(seq.subrange(0, i)) <= count_uppercase_sum(seq)
    decreases seq.len() - i
{
    if i == seq.len() {
        assert(seq.subrange(0, i) =~= seq);
    } else {
        /* code modified by LLM (iteration 5): fixed type casting for seq.len() in subrange call */
        let prefix = seq.subrange(0, i);
        let extended = seq.subrange(0, i + 1);
        let rest = seq.subrange(i + 1, seq.len() as int);
        
        count_uppercase_sum_prefix(seq, i + 1);
        
        assert(extended =~= prefix.push(seq[i]));
        count_uppercase_sum_append(prefix, seq[i]);
        
        if is_upper_case(seq[i]) {
            assert(count_uppercase_sum(extended) == count_uppercase_sum(prefix) + seq[i] as int);
            assert(seq[i] as int >= 0);
        } else {
            assert(count_uppercase_sum(extended) == count_uppercase_sum(prefix));
        }
        
        assert(count_uppercase_sum(extended) >= count_uppercase_sum(prefix));
        assert(count_uppercase_sum(extended) <= count_uppercase_sum(seq));
        assert(count_uppercase_sum(prefix) <= count_uppercase_sum(seq));
    }
}

fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures ret == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def digitSum(string: str) -> Nat"
docstring: |
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.
test_cases:
- input: ""
expected_output: 0
- input: "abAB"
expected_output: 131
- input: "helloE"
expected_output: 69
*/
// </vc-description>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
        decreases text.len() - i
    {
        let c = text[i];
        if is_upper_case_exec(c) {
            /* code modified by LLM (iteration 4): added overflow check and proof for invariant maintenance */
            proof {
                assert(c as int >= 65 && c as int <= 90);
                assert(c as u128 <= 90);
                assert(sum <= count_uppercase_sum(text@));
                count_uppercase_sum_prefix(text@, i as int);
                assert(count_uppercase_sum(text@.subrange(0, i as int)) <= count_uppercase_sum(text@));
            }
            sum = sum + (c as u128);
        }
        
        proof {
            /* code modified by LLM (iteration 4): improved proof for loop invariant */
            let old_prefix = text@.subrange(0, i as int);
            let new_prefix = text@.subrange(0, (i + 1) as int);
            
            assert(new_prefix =~= old_prefix.push(c));
            count_uppercase_sum_append(old_prefix, c);
            
            if is_upper_case(c) {
                assert(count_uppercase_sum(new_prefix) == count_uppercase_sum(old_prefix) + c as int);
                assert(sum == count_uppercase_sum(old_prefix) + c as u128);
                assert(c as int == c as u128);
            } else {
                assert(count_uppercase_sum(new_prefix) == count_uppercase_sum(old_prefix));
                assert(sum == count_uppercase_sum(old_prefix));
            }
            
            assert(sum == count_uppercase_sum(new_prefix));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    
    sum
}
// </vc-code>

} // verus!
fn main() {}