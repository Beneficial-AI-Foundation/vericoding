// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): extend invariant for not-found prefix up to i+1 */
proof fn lemma_extend_not_found(a: &Vec<i32>, key: i32, i: int)
    requires
        0 <= i,
        i < a.len() as int,
        forall|j: int| 0 <= j && j < i ==> a[j] != key,
        a[i] != key,
    ensures
        forall|j: int| 0 <= j && j < i + 1 ==> a[j] != key,
{
    assert forall|j: int| 0 <= j && j < i + 1 implies a[j] != key by {
        if j < i {
            assert(0 <= j && j < i);
        } else {
            assert(j == i);
            assert(a[i] != key);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): linear search with proper parentheses in int casts and strengthened invariants */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int),
            (i as int) <= (a.len() as int),
            forall|j: int| 0 <= j && j < (i as int) ==> a[j] != key,
        decreases (a.len() as int) - (i as int)
    {
        let v = a[i];
        proof { assert(a[i as int] == v); }
        if v == key {
            proof {
                assert(0 <= (i as int) && (i as int) < (a.len() as int));
                assert(a[i as int] == key);
            }
            #[verifier::truncate]
            let r: i32 = i as i32;
            return r;
        }
        proof {
            assert(a[i as int] == v);
            assert(v != key);
            lemma_extend_not_found(a, key, i as int);
        }
        i = i + 1;
    }
    proof {
        assert(i >= a.len());
        assert((i as int) >= (a.len() as int));
        assert((i as int) == (a.len() as int));
        assert forall|j: int| 0 <= j && j < (a.len() as int) implies a[j] != key by {
            assert(0 <= j && j < (a.len() as int));
            assert(j < (i as int));
        }
    }
    -1
}
// </vc-code>

}
fn main() {}