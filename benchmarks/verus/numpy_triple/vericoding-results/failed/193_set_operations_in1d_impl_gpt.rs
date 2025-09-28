// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate for membership in a sequence */
pub open spec fn exists_in_seq<T>(s: Seq<T>, x: T) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == x
}

/* helper modified by LLM (iteration 5): lemma deriving no-existence from universal inequality */
proof fn no_exists_from_forall_neq<T>(s: Seq<T>, x: T)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] != x,
    ensures
        !exists|k: int| 0 <= k < s.len() && s[k] == x,
{
}

/* helper modified by LLM (iteration 5): executable membership check with correctness proof */
fn contains_in_vec<T: PartialEq>(v: &Vec<T>, x: &T) -> (b: bool)
    ensures
        b == exists|j: int| 0 <= j < v@.len() && v@[j] == *x,
{
    let mut j: usize = 0;
    let mut found: bool = false;
    while j < v.len()
        invariant
            j as int <= v@.len(),
            found ==> exists|k: int| 0 <= k < j as int && v@[k] == *x,
            !found ==> forall|k: int| 0 <= k < j as int ==> v@[k] != *x,
        decreases (v.len() - j) as int
    {
        proof {
            assert(v@.len() == v.len() as int);
            assert(j as int < v@.len());
        }
        if v[j] == *x {
            proof {
                assert(v@[j as int] == v[j]);
                assert(v@[j as int] == *x);
            }
            found = true;
        } else {
            proof {
                assert(v@[j as int] == v[j]);
                assert(v@[j as int] != *x);
            }
        }
        j = j + 1;
    }
    proof {
        assert(j == v.len());
        assert(v@.len() == v.len() as int);
        if found {
            assert(exists|k: int| 0 <= k < v@.len() && v@[k] == *x);
        } else {
            assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] != *x);
            no_exists_from_forall_neq::<T>(v@, *x);
        }
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1@.len() ==> 
            result@[i] == exists|j: int| 0 <= j < ar2@.len() && ar1@[i] == ar2@[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement in1d using contains_in_vec and a loop maintaining correspondence invariant */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            i as int <= ar1@.len(),
            res@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> res@[k] == exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j],
        decreases (ar1.len() - i) as int
    {
        let b = contains_in_vec(&ar2, &ar1[i]);
        proof {
            assert(ar1@.len() == ar1.len() as int);
            assert(i as int < ar1@.len());
            assert(ar1@[i as int] == ar1[i]);
        }
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}