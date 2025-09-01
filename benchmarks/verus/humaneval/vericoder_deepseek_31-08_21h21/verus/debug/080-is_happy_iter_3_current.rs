use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
proof fn lemma_index_valid(s: Seq<char>, i: int) 
    requires
        0 <= i < s.len(),
    ensures
        s[i] is char,
{
}

proof fn lemma_three_distinct_implies_happy(s: Seq<char>)
    requires
        s.len() >= 3,
        forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i),
    ensures
        happy_spec(s),
{
}

proof fn lemma_not_three_distinct_implies_not_happy(s: Seq<char>, i: int)
    requires
        0 < i && i + 1 < s.len(),
        !three_distinct_spec(s, i),
    ensures
        !happy_spec(s),
{
}

spec fn is_happy_invariant(s: &Vec<char>, i: int) -> bool {
    i >= 0 && i <= s.len() as int - 2 &&
    (forall|j: int| 0 < j && j < i ==> three_distinct_spec(s@, j))
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if s.len() < 3 {
        return false;
    }
    
    let mut i: usize = 1;
    while i < s.len() - 1
        invariant
            1 <= i <= s.len(),
            is_happy_invariant(s, i as int),
    {
        assert(0 < i as int && i as int + 1 < s.len() as int) by {
            proof {
                assert(i < s.len() - 1 ==> i as int + 1 < s.len() as int);
            }
        }
        
        proof {
            lemma_index_valid(s@, i as int - 1);
            lemma_index_valid(s@, i as int);
            lemma_index_valid(s@, i as int + 1);
        }
        
        if s[i - 1] == s[i] || s[i] == s[i + 1] || s[i - 1] == s[i + 1] {
            assert(!three_distinct_spec(s@, i as int));
            proof {
                lemma_not_three_distinct_implies_not_happy(s@, i as int);
            }
            return false;
        }
        
        assert(three_distinct_spec(s@, i as int));
        i = i + 1;
    }
    
    proof {
        assert(forall|j: int| 0 < j && j < s.len() as int - 1 ==> three_distinct_spec(s@, j));
        assert(happy_spec(s@));
    }
    
    true
}
// </vc-code>

fn main() {}
}