use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// <vc-helpers>
fn vec_contains(v: &Vec<i32>, x: i32) -> bool
    ensures
        ret == in_array(v@, x)
{
    let mut i: int = 0;
    let mut found: bool = false;
    while i < v.len() 
        invariant
            0 <= i <= v.len(),
            // if found then there exists a witness m < i with v@[m] == x
            (found ==> exists|m: int| 0 <= m < i && v@[m] == x),
            // if not found then no witness exists among indices < i
            (!found ==> forall|m: int| 0 <= m < i ==> v@[m] != x)
    {
        let y: i32 = v.get(i);
        if !found {
            if y == x {
                found = true;
                // we can assert witness i
                assert(exists|m: int| 0 <= m < i+1 && v@[m] == x);
            }
        }
        i += 1;
    }
    // now i == v.len()
    // prove found <=> exists m < v.len() with v@[m] == x
    if found {
        // from invariant, exists m < i == v.len()
        assert(exists|m: int| 0 <= m < v.len() && v@[m] == x);
    } else {
        // from invariant, forall m < i == v.len() v@[m] != x
        assert(forall|m: int| 0 <= m < v.len() ==> v@[m] != x);
    }
    found
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut c: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            // every element currently in c came from some index < i of a and is not in b
            forall|k: int|
                0 <= k < c.len() ==>
                    in_array(a@, c@[k]) && !in_array(b@, c@[k]) &&
                    (exists|m: int| 0 <= m < i && a@[m] == c@[k]),
            // c has pairwise distinct elements
            forall|p: int, q: int| 0 <= p < q < c.len() ==> c@[p] != c@[q]
    {
        let x: i32 = a.get(i);
        let in_b: bool = vec_contains(b, x);
        let in_c: bool = vec_contains(&c, x);
        if !in_b && !in_c {
            // push x (which equals a@[i]) into c
            c.push(x);
            // After pushing, show the newly added element satisfies required properties
            // New element index is old c.len()-1
            let new_idx: int = c.len() - 1;
            // c@[new_idx] == x == a@[i]
            assert(c.get(new_idx) == x);
            assert(a.get(i) == x);
            // hence exists m < i+1 with a@[m] == c@[new_idx] (take m = i)
            assert(exists|m: int| 0 <= m < i + 1 && a@[m] == c@[new_idx]);
            // not in b: in_b == in_array(b@, x) by vec_contains ensures
            assert(!in_array(b@, x));
            // uniqueness: since in_c was false before push, no previous element equals x
            assert(forall|p: int| 0 <= p < new_idx ==> c@[p] != c@[new_idx]);
        }
        i += 1;
    }
    c
    // impl-end
}
// </vc-code>

fn main() {}
}