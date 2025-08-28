use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_fold_left_invariant(brackets: Seq<char>, i: nat)
    requires i <= brackets.len()
    ensures 
        spec_bracketing_helper(brackets.subrange(0, i as int)).1 == 
        (forall|j: int| 0 <= j < i ==> {
            let partial = spec_bracketing_helper(brackets.subrange(0, j + 1));
            partial.0 >= 0
        })
    decreases brackets.len() - i
{
    if i == 0 {
        assert(brackets.subrange(0, 0) == Seq::<char>::empty());
    } else {
        lemma_fold_left_invariant(brackets, (i - 1) as nat);
    }
}

proof fn lemma_helper_correctness(brackets: Seq<char>, balance: i32, valid: bool, i: usize)
    requires 
        i <= brackets.len(),
        balance as int == spec_bracketing_helper(brackets.subrange(0, i as int)).0,
        valid == spec_bracketing_helper(brackets.subrange(0, i as int)).1
    ensures
        valid <==> (forall|j: int| 0 <= j < i ==> {
            spec_bracketing_helper(brackets.subrange(0, j + 1)).0 >= 0
        })
{
    lemma_fold_left_invariant(brackets, i as nat);
}
// </vc-helpers>

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
    let mut balance: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            i <= brackets.len(),
            balance as int == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
            valid == spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
    {
        let c = brackets.as_bytes()[i] as char;
        
        match c {
            '<' => {
                balance = balance + 1;
            },
            '>' => {
                balance = balance - 1;
                if balance < 0 {
                    valid = false;
                }
            },
            _ => {
                // do nothing for other characters
            }
        }
        
        i = i + 1;
    }
    
    valid && balance == 0
}
// </vc-code>

} // verus!
fn main() {}