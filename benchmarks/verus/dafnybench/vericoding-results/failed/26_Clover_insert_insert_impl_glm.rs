use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_insert_preserves_len(line: &Vec<char>, l: int, nl: &Vec<char>, p: int, at: int)
    requires
        0 <= l + p <= line.len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
    ensures
        l + p == (l - at) + at + p
{
    assert(l + p == (l - at) + at + p);
}

proof fn lemma_index_bounds(line: &Vec<char>, l: int, nl: &Vec<char>, p: int, at: int, i: int)
    requires
        0 <= l + p <= line.len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
        0 <= i < p,
    ensures
        0 <= at + i < l + p,
        0 <= i < nl.len()
{
    assert(at + i <= at + p <= l + p);
    assert(i < p && p <= nl.len());
}

proof fn lemma_old_index_bounds(line: &Vec<char>, l: int, nl: &Vec<char>, p: int, at: int, i: int)
    requires
        0 <= l + p <= line.len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
        0 <= i < at,
    ensures
        0 <= i < line.len(),
        i < at <= l <= l + p
{
    assert(i < at && at <= l && l <= l + p);
}

proof fn lemma_shifted_index_bounds(line: &Vec<char>, l: int, nl: &Vec<char>, p: int, at: int, i: int)
    requires
        0 <= l + p <= line.len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
        at + p <= i < l + p,
    ensures
        0 <= i - p < line.len(),
        i - p >= at,
        i - p < l
{
    assert(i >= at + p ==> i - p >= at);
    assert(i < l + p ==> i - p < l);
    assert(l <= line.len());
}
// </vc-helpers>

// <vc-spec>
fn insert(line: &mut Vec<char>, l: int, nl: &Vec<char>, p: int, at: int)
    requires 
        0 <= l + p <= old(line).len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
    ensures 
        forall|i: int| (0 <= i < p) ==> line[at + i] == nl[i],
        forall|i: int| (0 <= i < at) ==> line[i] == old(line)[i],
        forall|i: int| (at + p <= i < l + p) ==> line[i] == old(line)[i - p],
// </vc-spec>
// <vc-code>
{
    lemma_insert_preserves_len(line, l, nl, p, at);
    
    let ghost old_line = old(line);
    
    proof {
        assert forall|i: int| (0 <= i < at) implies line@[i] == old_line@[i] by {
            lemma_old_index_bounds(old_line, l, nl, p, at, i);
            assert(line@[i] == old_line@[i]);
        }
    }
    
    for i in 0..(p as usize)
        invariant
            line.len() == (l + p) as usize,
            forall|j: int| (0 <= j < i as int) ==> line@[at + j] == nl@[j],
            forall|j: int| (0 <= j < at) ==> line@[j] == old_line@[j],
            forall|j: int| (at + i as int <= j < l + (p - i as int)) ==> old_line@[j] == line@[j + i as int],
            forall|j: int| (l + (p - i as int) <= j < l + p) ==> line@[j] == old_line@[j - (i as int)]
    {
        lemma_index_bounds(old_line, l, nl, p, at, i as int);
        line.set((at + (i as int)).to_usize(), nl[i]);
        
        proof {
            assert forall|j: int| (at + (i as int) + 1 <= j < l + (p - (i as int + 1))) implies old_line@[j] == line@[j + (i as int + 1)] by {
                let j_prime = j + 1;
                assert(old_line@[j_prime - 1] == line@[j_prime + (i as int) - 1]);
                assert(old_line@[j] == line@[j + (i as int + 1)]);
            }
            
            assert forall|j: int| (l + (p - (i as int + 1)) <= j < l + p) implies line@[j] == old_line@[j - ((i as int) + 1)] by {
                if j >= l + (p - (i as int + 1)) {
                    if j >= l + (p - i as int) {
                        assert(line@[j] == old_line@[j - (i as int)]);
                        assert(old_line@[j - (i as int)] == old_line@[j - ((i as int) + 1)]);
                        assert(line@[j] == old_line@[j - ((i as int) + 1)]);
                    } else {
                        assert(old_line@[j] == line@[j + i as int]);
                        assert(line@[j + i as int] == old_line@[j + i as int - ((i as int) + 1)]);
                        assert(line@[j] == old_line@[j - 1]);
                    }
                }
            }
        }
    }
    
    proof {
        assert forall|i: int| (0 <= i < p) implies line@[at + i] == nl@[i] by {
            lemma_index_bounds(old_line, l, nl, p, at, i);
            assert(line@[at + i] == nl@[i]);
        }
        
        assert forall|i: int| (0 <= i < at) implies line@[i] == old_line@[i] by {
            lemma_old_index_bounds(old_line, l, nl, p, at, i);
            assert(line@[i] == old_line@[i]);
        }
        
        assert forall|i: int| (at + p <= i < l + p) implies line@[i] == old_line@[i - p] by {
            lemma_shifted_index_bounds(old_line, l, nl, p, at, i);
            assert(line@[i] == old_line@[i - p]);
        }
    }
}
// </vc-code>

fn main() {
}

}