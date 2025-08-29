use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (ret:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_spec_bracketing_helper_properties(brackets: Seq<char>)
    ensures
        forall |i: int| 0 <= i <= brackets.len() ==> {
            let prefix = brackets.subrange(0, i);
            let (count, valid) = spec_bracketing_helper(prefix);
            count >= 0 || !valid
        }
{
    let f = |p: (int, bool), c: char| {
        let (x, b) = p;
        match c {
            '(' => (x + 1, b),
            ')' => (x - 1, b && x - 1 >= 0),
            _ => (x, b),
        }
    };
    
    assert forall |i: int| 0 <= i <= brackets.len() implies {
        let prefix = brackets.subrange(0, i);
        let (count, valid) = spec_bracketing_helper(prefix);
        count >= 0 || !valid
    } by {
        let prefix = brackets.subrange(0, i);
        let (count, valid) = spec_bracketing_helper(prefix);
        
        if i == 0 {
            assert(prefix.len() == 0);
            assert((count, valid) == (0, true));
        } else {
            let prev_prefix = brackets.subrange(0, i - 1);
            let (prev_count, prev_valid) = spec_bracketing_helper(prev_prefix);
            let c = brackets[i - 1];
            
            match c {
                '(' => {
                    assert((count, valid) == (prev_count + 1, prev_valid));
                }
                ')' => {
                    assert((count, valid) == (prev_count - 1, prev_valid && prev_count - 1 >= 0));
                    if valid {
                        assert(prev_count - 1 >= 0);
                        assert(count >= 0);
                    }
                }
                _ => {
                    assert((count, valid) == (prev_count, prev_valid));
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def correct_bracketing(brackets: str) -> Bool"
docstring: |
brackets is a string of "(" and ")".
return True if every opening bracket has a corresponding closing bracket.
test_cases:
- input: "("
expected_output: False
- input: "()"
expected_output: True
- input: "(()())"
expected_output: True
- input: ")(()"
expected_output: False
*/
// </vc-description>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)
    // pre-conditions-start
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> spec_bracketing(brackets@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 5): fixed invariant syntax by removing block structure */
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            i <= i32::MAX,
            valid ==> count >= 0,
            {
                let prefix = brackets@.subrange(0, i as int);
                let (spec_count, spec_valid) = spec_bracketing_helper(prefix);
                count == spec_count && valid == spec_valid
            },
    {
        proof {
            lemma_spec_bracketing_helper_properties(brackets@);
        }
        
        let c = brackets.as_bytes()[i] as char;
        
        match c {
            '(' => {
                count = count + 1;
            }
            ')' => {
                count = count - 1;
                if count < 0 {
                    valid = false;
                }
            }
            _ => {}
        }
        
        i = i + 1;
        
        proof {
            let current_prefix = brackets@.subrange(0, i as int);
            let prev_prefix = brackets@.subrange(0, (i - 1) as int);
            assert(current_prefix == prev_prefix.push(c));
        }
    }
    
    proof {
        let full_seq = brackets@.subrange(0, brackets@.len());
        assert(full_seq == brackets@);
        let (final_count, final_valid) = spec_bracketing_helper(brackets@);
        assert(count == final_count && valid == final_valid);
        assert(spec_bracketing(brackets@) == (final_valid && final_count == 0));
    }
    
    valid && count == 0
}
// </vc-code>

} // verus!
fn main() {}