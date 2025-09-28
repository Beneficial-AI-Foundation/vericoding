// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn median_string(s: Seq<char>, t: Seq<char>, k: int) -> Seq<char> {
    let s_val = string_to_base26(s);
    let t_val = string_to_base26(t);
    let median_val = (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}

spec fn string_to_base26(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { ((s[0] as int - 'a' as int) * pow26((s.len() - 1) as nat) + string_to_base26(s.subrange(1, s.len() as int))) as nat }
}

spec fn base26_to_string(val: nat, k: int) -> Seq<char>
    decreases k when k >= 1
{
    if k == 1 { seq![((val % 26) + ('a' as int)) as char] }
    else { base26_to_string(val / 26, k - 1).add(seq![((val % 26) + ('a' as int)) as char]) }
}

spec fn pow26(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 26 * pow26((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove base26_to_string returns a sequence of length k */
proof fn base26_to_string_len_lemma(val: nat, k: int)
    requires
        k >= 1,
    ensures
        base26_to_string(val, k).len() == k,
{
    if k == 1 {
        assert(base26_to_string(val, 1).len() == 1);
    } else {
        base26_to_string_len_lemma(val / 26, k - 1);
        let s1 = base26_to_string(val / 26, k - 1);
        let s2 = seq![((val % 26) + ('a' as int)) as char];
        assert(s2.len() == 1);
        assert(base26_to_string(val, k) == s1.add(s2));
        assert(s1.add(s2).len() == s1.len() + s2.len());
        assert(base26_to_string(val, k).len() == (k - 1) + 1);
    }
}

/* helper modified by LLM (iteration 5): prove all chars in base26_to_string are lowercase */
proof fn base26_to_string_chars_lowercase_lemma(val: nat, k: int)
    requires
        k >= 1,
    ensures
        forall|i: int| 0 <= i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z',
{
    if k == 1 {
        let r = val % 26;
        assert(0 <= r && r < 26);
        let ch = ((r) + ('a' as int)) as char;
        assert(base26_to_string(val, 1) == seq![ch]);
        assert('a' <= ch && ch <= 'z');
    } else {
        base26_to_string_len_lemma(val / 26, k - 1);
        base26_to_string_chars_lowercase_lemma(val / 26, k - 1);
        assert(forall|i: int| 0 <= i && i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z') by {
            let i: int;
            if 0 <= i && i < k {
                let s1 = base26_to_string(val / 26, k - 1);
                let last = (((val % 26) + ('a' as int)) as char);
                let s = s1.add(seq![last]);
                assert(base26_to_string(val, k) == s);
                if i < k - 1 {
                    assert(s1.len() == k - 1);
                    assert('a' <= s1[i] && s1[i] <= 'z');
                    assert(s[i] == s1[i]);
                } else {
                    assert(i == k - 1);
                    assert(s1.len() == k - 1);
                    let r = val % 26;
                    assert(0 <= r && r < 26);
                    assert('a' <= last && last <= 'z');
                    assert(seq![last].len() == 1);
                    assert(s[i] == seq![last][0]);
                    assert(seq![last][0] == last);
                }
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(k: usize, s: Vec<char>, t: Vec<char>) -> (result: Vec<char>)
    requires 
        k >= 1,
        s.len() == k,
        t.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] s[i] <= 'z',
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] t[i] <= 'z',
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] result[i] <= 'z',
        result@ == median_string(s@, t@, k as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace Vec::from_seq with Vec::from for constructing from sequence */
    let ghost res_seq = median_string(s@, t@, k as int);
    proof {
        let val_m = (string_to_base26(s@) + string_to_base26(t@)) / 2;
        base26_to_string_len_lemma(val_m, k as int);
        base26_to_string_chars_lowercase_lemma(val_m, k as int);
        assert(res_seq == base26_to_string(val_m, k as int));
    }
    let result: Vec<char> = Vec::from(res_seq);
    result
}
// </vc-code>


}

fn main() {}