// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 10 && 
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1' || s[i] == 'B'
}

spec fn simulate_keystrokes(keystrokes: Seq<char>) -> Seq<char>
    decreases keystrokes.len()
{
    if keystrokes.len() == 0 {
        Seq::<char>::empty()
    } else {
        let prev = simulate_keystrokes(keystrokes.subrange(0, keystrokes.len() - 1));
        let last_key = keystrokes[keystrokes.len() - 1];
        if last_key == 'B' {
            if prev.len() > 0 {
                prev.subrange(0, prev.len() - 1)
            } else {
                prev
            }
        } else {
            prev.push(last_key)
        }
    }
}

spec fn valid_output(result: Seq<char>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> result[i] == '0' || result[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove iterative and recursive approaches are equivalent */
proof fn lemma_simulate_incremental(keystrokes: Seq<char>, i: int)
    requires
        0 <= i < keystrokes.len(),
    ensures
        simulate_keystrokes(keystrokes.subrange(0, i + 1)) == {
            let prev = simulate_keystrokes(keystrokes.subrange(0, i));
            let key = keystrokes[i];
            if key == 'B' {
                if prev.len() > 0 {
                    prev.subrange(0, prev.len() - 1)
                } else {
                    prev
                }
            } else {
                prev.push(key)
            }
        },
    decreases i + 1,
{
    let sub = keystrokes.subrange(0, i + 1);
    assert(sub.len() == i + 1);
    assert(sub.subrange(0, sub.len() - 1) == keystrokes.subrange(0, i));
    assert(sub[sub.len() - 1] == keystrokes[i]);
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(s@),
    ensures 
        valid_output(result@),
        result@ == simulate_keystrokes(s@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added proof block with lemma call to verify invariant */
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            valid_input(s@),
            valid_output(result@),
            result@ == simulate_keystrokes(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let key = s[i];
        
        proof {
            lemma_simulate_incremental(s@, i as int);
        }
        
        if key == 'B' {
            if result.len() > 0 {
                result.pop();
            }
        } else {
            result.push(key);
        }
        
        i = i + 1;
    }
    
    assert(i == s.len());
    assert(s@.subrange(0, i as int) == s@);
    
    result
}
// </vc-code>


}

fn main() {}