use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
proof fn lemma_replace_with_colon(s: &str, i: int, v: String)
    requires
        s@.len() == v@.len(),
        0 <= i < s@.len(),
        forall|j: int| 0 <= j < i ==> (v@[j] == if is_space_comma_dot(s@[j]) { ':' } else { s@[j] })
    ensures
        forall|j: int| 0 <= j < i + 1 ==> (v@[j] == if is_space_comma_dot(s@[j]) { ':' } else { s@[j] })
{
    let ghost v_old = v@;
    assert(forall|j: int| 0 <= j < i ==> (v@[j] == if is_space_comma_dot(s@[j]) { ':' } else { s@[j] }));
    assert(v@[i] == if is_space_comma_dot(s@[i]) { ':' } else { s@[i] });
    assert(forall|j: int| 0 <= j < i + 1 ==> (v@[j] == if is_space_comma_dot(s@[j]) { ':' } else { s@[j] }));
}

proof fn lemma_string_push(seq: Seq<char>, c: char) {
    ensures(|s: String| s@.len() == (seq + Seq::singleton(c)).len());
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut v: String = String::new();
    let mut i: usize = 0;
    let s_len = s.len();

    proof {
        assert(s@.len() == s_len);
    }

    while i < s_len
        invariant
            0 <= i <= s_len,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> (v@[j] == if is_space_comma_dot(s@[j]) { ':' } else { s@[j] })
    {
        let c: char = s.chars().nth(i).unwrap();
        let new_char: char = if is_space_comma_dot(c) { ':' } else { c };
        let ghost old_v = v@;
        v.push(new_char);
        
        proof {
            lemma_string_push(old_v, new_char);
            lemma_replace_with_colon(s, i as int, v);
        }

        i = i + 1;
    }

    proof {
        assert(s@.len() == s_len);
        assert(v@.len() == s_len);
        assert(forall|i: int| 0 <= i < s_len ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        });
    }

    v
}
// </vc-code>

fn main() {}

}