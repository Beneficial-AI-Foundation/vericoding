use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_modular_arithmetic(len: int, n: int, i: int)
    requires 
        len > 0,
        0 <= n < len,
        0 <= i < len
    ensures 
        (i + n) % len == if i + n < len { i + n } else { i + n - len }
{
    if i + n < len {
        assert((i + n) % len == i + n);
    } else {
        assert(0 <= i + n - len < len);
        assert((i + n) % len == i + n - len);
    }
}

proof fn lemma_seq_concat_len<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        (s1 + s2).len() == s1.len() + s2.len()
{
    assert((s1 + s2).len() == s1.len() + s2.len());
}

proof fn lemma_seq_subrange<T>(s: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= s.len()
    ensures
        s.subrange(start, end).len() == end - start,
        forall|i: int| 0 <= i < (end - start) ==> s.subrange(start, end)[i] == s[start + i]
{
    assert(s.subrange(start, end).len() == end - start);
    assert forall |i: int| 0 <= i < (end - start) implies #[trigger] s.subrange(start, end)[i] == s[start + i] by {
        assert(s.subrange(start, end)[i] == s[start + i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let len = l.len();
    let part1 = l.subrange(n, len);
    let part2 = l.subrange(0, n);
    let r = part1 + part2;
    proof {
        lemma_seq_subrange(l, n, len);
        lemma_seq_subrange(l, 0, n);
        lemma_seq_concat_len(part1, part2);
        
        let mid = len - n;
        assert forall |i: int| 0 <= i < mid implies #[trigger] r[i] == l[(i + n) % len] by {
            assert(r[i] == part1[i]);
            assert(part1[i] == l[n + i]);
            lemma_modular_arithmetic(len, n, i);
            assert((i + n) % len == i + n);
            assert(l[n + i] == l[(i + n) % len]);
        };
        assert forall |i: int| mid <= i < len implies #[trigger] r[i] == l[(i + n) % len] by {
            let j = i - mid;
            assert(r[i] == part2[j]);
            assert(part2[j] == l[j]);
            lemma_modular_arithmetic(len, n, i);
            assert((i + n) % len == i + n - len);
            assert(j == i + n - len);
            assert(l[j] == l[(i + n) % len]);
        };
    }
    r
}
// </vc-code>

fn main() {
}

}