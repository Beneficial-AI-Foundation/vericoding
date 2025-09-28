// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn count_as(s: Seq<char>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else if s[0] == 'a' {
            1 + count_as(s.subrange(1, s.len() as int))
        } else {
            count_as(s.subrange(1, s.len() as int))
        }
    }
    
    spec fn remove_as(s: Seq<char>) -> Seq<char>
        decreases s.len()
    {
        if s.len() == 0 {
            seq![]
        } else if s[0] == 'a' {
            remove_as(s.subrange(1, s.len() as int))
        } else {
            seq![s[0]].add(remove_as(s.subrange(1, s.len() as int)))
        }
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating lengths of remove_as and count_as */
proof fn remove_as_len(s: Seq<char>)
    ensures
        (remove_as(s).len() as int) + count_as(s) == s.len() as int,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        remove_as_len(tail);
        if s[0] == 'a' {
            proof {
                assert(remove_as(s) == remove_as(tail));
                assert(count_as(s) == 1 + count_as(tail));
                assert((remove_as(tail).len() as int) + count_as(tail) == tail.len() as int);
            }
            assert((remove_as(s).len() as int) + count_as(s) == s.len() as int);
        } else {
            proof {
                assert(remove_as(s) == seq![s[0]].add(remove_as(tail)));
                assert(count_as(s) == count_as(tail));
                assert((remove_as(tail).len() as int) + count_as(tail) == tail.len() as int);
                assert(seq![s[0]].add(remove_as(tail)).len() == 1 + remove_as(tail).len());
            }
            assert((remove_as(s).len() as int) + count_as(s) == s.len() as int);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate runtime Vec t and push non-'a' chars using usize indices */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            res.len() <= t.len(),
        decreases t.len() - i
    {
        let c: char = t[i];
        if c != 'a' {
            res.push(c);
        }
        i += 1;
    }
    res
}
// </vc-code>


}

fn main() {}