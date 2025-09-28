// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn repeat_string_spec(s: Seq<char>, n: int) -> Seq<char> 
    decreases (if n <= 0 { 0 } else { n }) as nat
{
    if n <= 0 {
        Seq::<char>::empty()
    } else if n == 1 {
        s
    } else {
        s + repeat_string_spec(s, n - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma showing that appending one more copy advances repeat_string_spec by 1 */
proof fn lemma_repeat_snoc(s: Seq<char>, n: int)
    requires
        n >= 0,
    ensures
        repeat_string_spec(s, n) + s == repeat_string_spec(s, n + 1),
    decreases n
{
    if n == 0 {
        assert(repeat_string_spec(s, 0) == Seq::<char>::empty());
        assert(Seq::<char>::empty() + s == s);
        assert(repeat_string_spec(s, 1) == s);
    } else {
        // Induction step: use lemma for n-1 and associativity of sequence concatenation
        lemma_repeat_snoc(s, n - 1);
        assert(repeat_string_spec(s, n) == s + repeat_string_spec(s, n - 1));
        assert((s + repeat_string_spec(s, n - 1)) + s == s + (repeat_string_spec(s, n - 1) + s));
        assert(repeat_string_spec(s, n - 1) + s == repeat_string_spec(s, n));
        assert(s + (repeat_string_spec(s, n - 1) + s) == s + repeat_string_spec(s, n));
        assert(repeat_string_spec(s, n + 1) == s + repeat_string_spec(s, n));
    }
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<String>, i: Vec<i32>) -> (result: Vec<String>)
    requires a.len() == i.len(),
    ensures 
        result.len() == a.len(),
        /* Core property: Element-wise string repetition */
        forall|j: int| 0 <= j < a.len() ==> 
            result[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        /* Zero/negative repetition property: Always yields empty string */
        forall|j: int| 0 <= j < a.len() && i[j] <= 0 ==> 
            result[j]@ == Seq::<char>::empty(),
        /* Identity property: Multiplying by 1 yields the original string */
        forall|j: int| 0 <= j < a.len() && i[j] == 1 ==> 
            result[j] == a[j],
        /* Zero property: Multiplying by 0 yields empty string */
        forall|j: int| 0 <= j < a.len() && i[j] == 0 ==> 
            result[j]@ == Seq::<char>::empty(),
        /* Empty string property: Empty strings remain empty regardless of repetition */
        forall|j: int| 0 <= j < a.len() && a[j]@ == Seq::<char>::empty() ==> 
            result[j]@ == Seq::<char>::empty(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build repeated strings using push_str in a loop; avoid unsupported truncate */
    let mut res: Vec<String> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            res.len() == idx,
            idx <= a.len(),
            forall|j: int| 0 <= j < idx as int ==> res[j]@ == repeat_string_spec(a[j]@, i[j] as int),
        decreases (a.len() as int - idx as int)
    {
        let ssrc = &a[idx];
        let count: i32 = i[idx];
        let tmp: String;
        if count == 1 {
            let t = ssrc.clone();
            proof { assert(t@ == repeat_string_spec(ssrc@, 1)); }
            tmp = t;
        } else {
            let rep: i32 = if count <= 0 { 0 } else { count };
            let mut t = String::new();
            let mut k: i32 = 0;
            while k < rep
                invariant
                    0 <= k <= rep,
                    t@ == repeat_string_spec(ssrc@, k as int),
                decreases (rep as int - k as int)
            {
                t.push_str(ssrc.as_str());
                proof {
                    // From push_str's spec, t@ becomes old(t)@ + ssrc@; combine with lemma to advance k
                    lemma_repeat_snoc(ssrc@, k as int);
                }
                k += 1;
            }
            tmp = t;
            proof {
                if count <= 0 {
                    assert(rep == 0);
                    assert(repeat_string_spec(ssrc@, count as int) == Seq::<char>::empty());
                    assert(repeat_string_spec(ssrc@, rep as int) == Seq::<char>::empty());
                } else {
                    assert(rep == count);
                }
            }
        }
        let old_idx = idx;
        res.push(tmp);
        idx += 1;
        proof {
            assert(res[old_idx as int]@ == repeat_string_spec(a[old_idx as int]@, i[old_idx as int] as int));
        }
    }
    res
}
// </vc-code>


}
fn main() {}