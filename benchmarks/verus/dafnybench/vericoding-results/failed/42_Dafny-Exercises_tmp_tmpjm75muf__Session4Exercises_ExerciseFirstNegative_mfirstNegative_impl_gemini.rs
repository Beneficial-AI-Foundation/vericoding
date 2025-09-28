// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed 'forall...by' syntax error */
proof fn lemma_positive_extend(s: Seq<int>, x: int)
    requires
        positive(s),
        x >= 0,
    ensures
        positive(s.push(x))
{
    forall|i: int| 0 <= i < s.push(x).len() implies s.push(x)@[i] >= 0 {
        if i < s.len() {
        } else {
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion to explicitly prove invariant maintenance */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(v@.subrange(0, i as int)),
        decreases v.len() - i
    {
        if v[i] < 0 {
            return (true, i);
        }

        proof {
            lemma_positive_extend(v@.subrange(0, i as int), v[i]);
            assert(v@.subrange(0, (i + 1) as int) == v@.subrange(0, i as int).push(v[i]));
        }

        i = i + 1;
    }

    return (false, 0);
}
// </vc-code>

}
fn main() {}