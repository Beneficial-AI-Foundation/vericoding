use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_first_e_nonnegative(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        x >= 0,
{
}

proof fn lemma_first_e_index_in_bounds(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        x < a.len(),
{
}

proof fn lemma_first_e_is_e(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        a[x] == 'e',
{
}

proof fn lemma_first_e_no_prior_e(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
{
}

 proof fn lemma_first_e_bounds(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        0 <= x < a.len(),
{
    lemma_first_e_nonnegative(a, x);
    lemma_first_e_index_in_bounds(a, x);
}

 proof fn lemma_first_e_all_conditions(a: Seq<char>, x: int)
    requires
        0 <= x < a.len(),
        a[x] == 'e',
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
    ensures
        0 <= x < a.len() && a[x] == 'e' && 
        forall|i: int| 0 <= i < x ==> a[i] != 'e',
{
    lemma_first_e_bounds(a, x);
    lemma_first_e_is_e(a, x);
    lemma_first_e_no_prior_e(a, x);
}

proof fn lemma_not_contains_if_forall_not(a: Seq<char>, e: char)
    requires
        forall|i: int| 0 <= i < a.len() ==> a[i] != e,
    ensures
        !a.contains(e),
{
    if a.contains(e) {
        let i = choose|i| 0 <= i < a.len() && a[i] == e;
        assert(a[i] != e);
    }
}
// </vc-helpers>

// <vc-spec>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 0;
    let n = a.len() as int;
    
    while i < n
    {
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < (i as int) ==> a@[j] != 'e',
        
        if a[i as int] == 'e' {
            return i;
        }
        i = i + 1;
    }
    
    proof {
        lemma_not_contains_if_forall_not(a@, 'e');
    }
    
    -1
}
// </vc-code>

fn main() {
}

}