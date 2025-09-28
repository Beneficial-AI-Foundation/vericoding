// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'A' || s[i] == 'B' || s[i] == 'C' || s[i] == '.'
}

spec fn has_all_three_colors(s: Seq<char>, start: int) -> bool
    recommends 0 <= start <= s.len() - 3
{
    s.subrange(start, start + 3).contains('A') && 
    s.subrange(start, start + 3).contains('B') && 
    s.subrange(start, start + 3).contains('C')
}

spec fn possible_to_get_all_colors(s: Seq<char>) -> bool {
    s.len() >= 3 && exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: &[char]) -> (result: Vec<char>)
    requires 
        s@.len() >= 0 && forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'B' || s@[i] == 'C' || s@[i] == '.'
    ensures 
        result@ == seq!['Y', 'e', 's'] ==> possible_to_get_all_colors(s@),
        result@ == seq!['N', 'o'] ==> !possible_to_get_all_colors(s@),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int type errors by using usize for loop variables and casting to int in ghost code */
    if s.len() < 3 {
        return vec!['N','o'];
    }

    let len = s.len();
    let mut i = 0usize;

    while i < len - 2
        invariant 
            0 <= i as int <= len as int - 2,
            forall|j: int| 0 <= j < i as int ==> !has_all_three_colors(s@, j)
        decreases len as int - i as int
    {
        let c1 = s[i];
        let c2 = s[i+1];
        let c3 = s[i+2];

        let mut has_a = false;
        let mut has_b = false;
        let mut has_c = false;

        if c1 == 'A' { has_a = true; }
        else if c1 == 'B' { has_b = true; }
        else if c1 == 'C' { has_c = true; }

        if c2 == 'A' { has_a = true; }
        else if c2 == 'B' { has_b = true; }
        else if c2 == 'C' { has_c = true; }

        if c3 == 'A' { has_a = true; }
        else if c3 == 'B' { has_b = true; }
        else if c3 == 'C' { has_c = true; }

        if has_a && has_b && has_c {
            proof {
                let i_int = i as int;
                let sub = s@.subrange(i_int, i_int+3);
                // Relate the sequence elements to the variables
                assert(sub[0] == s@[i_int]);
                assert(sub[1] == s@[i_int+1]);
                assert(sub[2] == s@[i_int+2]);
                assert(sub[0] == c1);
                assert(sub[1] == c2);
                assert(sub[2] == c3);

                // Prove contains('A') if has_a is true
                if has_a {
                    if c1 == 'A' {
                        assert(sub[0] == 'A');
                    } else if c2 == 'A' {
                        assert(sub[1] == 'A');
                    } else {
                        assert(sub[2] == 'A');
                    }
                    assert(sub.contains('A'));
                }
                if has_b {
                    if c1 == 'B' {
                        assert(sub[0] == 'B');
                    } else if c2 == 'B' {
                        assert(sub[1] == 'B');
                    } else {
                        assert(sub[2] == 'B');
                    }
                    assert(sub.contains('B'));
                }
                if has_c {
                    if c1 == 'C' {
                        assert(sub[0] == 'C');
                    } else if c2 == 'C' {
                        assert(sub[1] == 'C');
                    } else {
                        assert(sub[2] == 'C');
                    }
                    assert(sub.contains('C'));
                }

                // Now we can assert that the substring has all three
                assert(has_all_three_colors(s@, i_int));
            }
            return vec!['Y','e','s'];
        } else {
            proof {
                let i_int = i as int;
                let sub = s@.subrange(i_int, i_int+3);
                assert(sub[0] == s@[i_int]);
                assert(sub[1] == s@[i_int+1]);
                assert(sub[2] == s@[i_int+2]);
                assert(sub[0] == c1);
                assert(sub[1] == c2);
                assert(sub[2] == c3);

                if !has_a {
                    // Then none of the three is 'A'
                    assert(c1 != 'A');
                    assert(c2 != 'A');
                    assert(c3 != 'A');
                    assert(sub[0] != 'A');
                    assert(sub[1] != 'A');
                    assert(sub[2] != 'A');
                    assert(!sub.contains('A'));
                }
                if !has_b {
                    assert(c1 != 'B');
                    assert(c2 != 'B');
                    assert(c3 != 'B');
                    assert(sub[0] != 'B');
                    assert(sub[1] != 'B');
                    assert(sub[2] != 'B');
                    assert(!sub.contains('B'));
                }
                if !has_c {
                    assert(c1 != 'C');
                    assert(c2 != 'C');
                    assert(c3 != 'C');
                    assert(sub[0] != 'C');
                    assert(sub[1] != 'C');
                    assert(sub[2] != 'C');
                    assert(!sub.contains('C'));
                }

                // Since we are in the else branch, we know at least one of has_a, has_b, has_c is false.
                // Therefore, at least one of the contains conditions fails, so has_all_three_colors is false.
                assert(!has_all_three_colors(s@, i_int));
            }
        }

        i += 1;
    }

    return vec!['N','o'];
}
// </vc-code>


}

fn main() {}