use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_push_property<T>(s: Seq<T>, x: T, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        (s.push(x))[i] == if i < s.len() { s[i] } else { x },
    decreases i,
{
    if i < s.len() {
        assert((s.push(x))[i] == s[i]);
    } else {
        assert(i == s.len());
        assert((s.push(x))[i] == x);
    }
}

spec fn spec_push<T>(s: Seq<T>, x: T) -> Seq<T> {
    s.push(x)
}
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (c: Vec<i32>)
    ensures c@ == a@ + seq![b]
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::<i32>::new();
    c = a.clone();
    
    proof {
        let ghost a_seq = a@;
        let ghost result_seq = a_seq.push(b);
        
        assert(c@ == a_seq);
    }
    
    let mut temp_vec = Vec::<i32>::new();
    temp_vec = c;
    temp_vec.push(b);
    c = temp_vec;
    
    proof {
        let ghost a_seq = a@;
        let ghost result_seq = a_seq.push(b);
        
        assert forall|i: int| 0 <= i < c@.len() implies c@[i] == result_seq[i] by {
            assert(0 <= i <= a_seq.len());
            lemma_seq_push_property(a_seq, b, i);
            if i < a_seq.len() {
                assert(c@[i] == a@[i]);
            } else {
                assert(i == a_seq.len());
                assert(c@[i] == b);
            }
        };
        
        assert(c@.len() == a_seq.len() + 1);
        assert(c@ == result_seq);
    }
    
    c
}
// </vc-code>

fn main() {
}

}