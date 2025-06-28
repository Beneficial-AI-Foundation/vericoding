use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int && c as int <= 57
}

spec fn count_digits_in_range(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end || start < 0 || start >= s.len() {
        0
    } else {
        let current_count = if IsDigit(s[start]) { 1 } else { 0 };
        current_count + count_digits_in_range(s, start + 1, end)
    }
}

// Helper lemma to prove the inductive step
proof fn lemma_count_digits_step(s: Seq<char>, i: int)
    requires 
        0 <= i < s.len(),
    ensures
        count_digits_in_range(s, 0, i + 1) == 
        count_digits_in_range(s, 0, i) + (if IsDigit(s[i]) { 1 } else { 0 }),
{
    if i == 0 {
        // Base case
        assert(count_digits_in_range(s, 0, 0) == 0);
        assert(count_digits_in_range(s, 0, 1) == (if IsDigit(s[0]) { 1 } else { 0 }));
    } else {
        // Inductive case - the recursive definition handles this
        lemma_count_digits_step(s, i - 1);
    }
}

fn CountDigits(s: Seq<char>) -> (count: int)
    ensures
        count >= 0,
        count == count_digits_in_range(s, 0, s.len() as int),
{
    let mut count = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == count_digits_in_range(s, 0, i as int),
    {
        // Prove the loop invariant will be maintained
        proof {
            lemma_count_digits_step(s, i as int);
        }
        
        if IsDigit(s[i as int]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}