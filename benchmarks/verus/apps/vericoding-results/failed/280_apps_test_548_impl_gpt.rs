// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_even(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0
}

spec fn has_odd(a: Seq<int>) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): establish correspondence between i8 and int modulo 2 */
proof fn lemma_cast_i8_int_mod2(x: i8)
    ensures
        ((x as int) % 2) == (x % 2) as int,
{
    assert(((x as int) % 2) == (x % 2) as int);
}

/* helper modified by LLM (iteration 2): map index equals applying the function at that index */
proof fn lemma_map_cast_index(s: Seq<i8>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.map(|j: int, x: i8| x as int)[i] == s[i] as int,
{
    assert(s.map(|j: int, x: i8| x as int)[i] == s[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: &'static str)
    ensures 
        (result == "Second") <==> all_even(a@.map(|i: int, x: i8| x as int)),
        (result == "First") <==> has_odd(a@.map(|i: int, x: i8| x as int)),
        result == "First" || result == "Second",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add quantifier triggers and use lemmas to relate i8 and int modulo */
    let mut i: usize = 0;
    let mut found: bool = false;

    while i < a.len()
        invariant
            i <= a.len(),
            found ==> (exists|k: int| 0 <= k < i as int && #[trigger] ((a@.map(|j: int, x: i8| x as int))[k] % 2 == 1)),
            !found ==> (forall|k: int| 0 <= k < i as int ==> #[trigger] ((a@.map(|j: int, x: i8| x as int))[k] % 2 == 0)),
        decreases a.len() - i
    {
        let idx = i;
        let ai = a[idx];
        if ai % 2 == 1 {
            found = true;
            i += 1;
            proof {
                lemma_cast_i8_int_mod2(ai);
                assert(a@.len() == a.len() as int);
                let k: int = idx as int;
                assert(0 <= k && k < a@.len());
                lemma_map_cast_index(a@, k);
                assert((a@.map(|j: int, x: i8| x as int))[k] == (ai as int));
                assert(((ai as int) % 2) == (ai % 2) as int);
                assert(((a@.map(|j: int, x: i8| x as int))[k]) % 2 == 1);
            }
        } else {
            i += 1;
            proof {
                lemma_cast_i8_int_mod2(ai);
                assert(a@.len() == a.len() as int);
                let k: int = (i - 1) as int;
                assert(0 <= k && k < a@.len());
                lemma_map_cast_index(a@, k);
                assert((a@.map(|j: int, x: i8| x as int))[k] == (ai as int));
                assert(((ai as int) % 2) == (ai % 2) as int);
                assert(((a@.map(|j: int, x: i8| x as int))[k]) % 2 == 0);
            }
        }
    }

    let result = if found { "First" } else { "Second" };

    proof {
        assert(i == a.len());
        if found {
            assert(exists|k: int| 0 <= k < i as int && #[trigger] ((a@.map(|j: int, x: i8| x as int))[k] % 2 == 1));
        } else {
            assert(forall|k: int| 0 <= k < i as int ==> #[trigger] ((a@.map(|j: int, x: i8| x as int))[k] % 2 == 0));
        }
    }

    result
}
// </vc-code>


}

fn main() {}