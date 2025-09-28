use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_to_vec_char(s: Seq<char>) -> Vec<char> {
    let mut v: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while (i < s.len())
        invariant
            i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v.index(j) == s.index(j),
            s.len() == v.len() + (s.len() - i as int),
    {
        v.push(s.index(i));
        i = i + 1;
    }
    v
}

fn vec_to_seq_char(v: Vec<char>) -> Seq<char> {
    let mut s: Seq<char> = Seq::new();
    let mut i: nat = 0;
    while (i < v.len())
        invariant
            i <= v.len(),
            s.len() == i,
            forall|j: int| 0 <= j < i ==> s.index(j) == v.index(j),
            v.len() == s.len() + (v.len() - i as int),
    {
        s = s.push(v.index(i));
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn replace_chars(s: Seq<char>, old_char: char, new_char: char) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i]),
// </vc-spec>
// <vc-code>
{
    let mut vec_s = seq_to_vec_char(s);
    let mut i: nat = 0;
    while (i < vec_s.len())
        invariant
            i <= vec_s.len(),
            vec_s.len() == s.len(),
            forall|j: int| 0 <= j < i ==>
                (s.index(j) == old_char ==> vec_s.index(j) == new_char) &&
                (s.index(j) != old_char ==> vec_s.index(j) == s.index(j)),
            forall|j: int| i <= j < vec_s.len() ==> vec_s.index(j) == s.index(j),
    {
        if vec_s.index(i) == old_char {
            vec_s.set(i, new_char);
        }
        i = i + 1;
    }
    vec_to_seq_char(vec_s)
}
// </vc-code>

fn main() {
}

}