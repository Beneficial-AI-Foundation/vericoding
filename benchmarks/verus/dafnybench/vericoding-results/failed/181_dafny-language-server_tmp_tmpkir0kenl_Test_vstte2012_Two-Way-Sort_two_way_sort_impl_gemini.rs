// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

spec fn multisets<T>(s: Seq<T>) -> Multiset<T>
    decreases s.len(),
{
    if s.len() == 0 { 
        Multiset::empty() 
    } else { 
        Multiset::singleton(s[0]).add(multisets(s.subrange(1, s.len() as int)))
    }
}

fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < j < old(a).len(),
    ensures 
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m],
        multisets(a@) == multisets(old(a)@),
{
    assume(false);
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed chained comparison and trailing comma syntax in requires */
proof fn lemma_partition_implies_sorted(a: Seq<bool>, i: int, j: int)
    requires
        i >= j,
        forall|k: int| 0 <= k && k < i ==> !a[k],
        forall|k: int| j < k && k < a.len() ==> a[k]
    ensures
        forall|m: int, n: int| 0 <= m && m < n && n < a.len() ==> (!a[m] || a[n]),
{
    assert forall|m: int, n: int| 0 <= m && m < n && n < a.len() implies !a[m] || a[n] by {
        if a[m] {
            assert(m >= i);
            assert(a[n]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn two_way_sort(a: &mut Vec<bool>)
    ensures 
        forall|m: int, n: int| 0 <= m < n < a.len() ==> (!a[m] || a[n]),
        multisets(a@) == multisets(old(a)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added missing comma between loop invariants */
    let ghost original_a_spec = a@;
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    while i < j
        invariant
            a.len() == n,
            multisets(a@) == multisets(original_a_spec),
            i as int <= j as int + 1,
            j < n,
            forall|k: int| 0 <= k && k < i as int ==> !a@[k],
            forall|k: int| j as int < k && k < n as int ==> a@[k]
        decreases (j - i)
    {
        if !a[i] {
            i = i + 1;
        } else if a[j] {
            j = j - 1;
        } else {
            assert(a[i]);
            assert(!a[j]);
            
            let ghost pre_swap_a = a@;

            let temp = a[i];
            a.set(i, a[j]);
            a.set(j, temp);

            proof {
                vstd::seq_lib::lemma_swap_maintains_multiset(pre_swap_a, i as int, j as int);
            }
            
            i = i + 1;
            j = j - 1;
        }
    }
    
    lemma_partition_implies_sorted(a@, i as int, j as int);
}
// </vc-code>

}
fn main() {}