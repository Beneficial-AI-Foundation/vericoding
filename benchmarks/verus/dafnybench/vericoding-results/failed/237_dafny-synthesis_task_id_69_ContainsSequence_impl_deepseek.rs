use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_eq_index<A>(s1: Seq<A>, s2: Seq<A>) 
    requires s1 =~= s2
    ensures forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
{
}

proof fn lemma_seq_eq_len<A>(s1: Seq<A>, s2: Seq<A>) 
    requires s1 =~= s2
    ensures s1.len() == s2.len()
{
}

spec fn equal_at_index<A>(s1: Seq<A>, s2: Seq<A>, i: int) -> bool {
    if 0 <= i < s1.len() && 0 <= i < s2.len() {
        s1[i] == s2[i]
    } else {
        false
    }
}

proof fn seq_eq_implies_equal_at_all_indices<A>(s1: Seq<A>, s2: Seq<A>)
    requires s1 =~= s2
    ensures forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
{
    lemma_seq_eq_len(s1, s2);
    lemma_seq_eq_index(s1, s2);
}

proof fn lemma_nat_to_int(n: nat)
    ensures n as int >= 0
{
}

proof fn lemma_nat_lt_implies_int_lt(i: nat, j: nat)
    requires i < j
    ensures (i as int) < (j as int)
{
}
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    let mut found = false;
    let mut j: nat = 0;
    while j < list.len()
        invariant
            0 <= j <= list.len(),
            found ==> exists|i: int| 0 <= i < j && sub == list[i],
            !found ==> forall|i: int| 0 <= i < j ==> sub != list[i]
    {
        if sub =~= list[j] {
            proof {
                lemma_nat_to_int(j);
                seq_eq_implies_equal_at_all_indices(sub, list[j]);
                assert(sub == list[j]);
            }
            found = true;
        } else {
            proof {
                assert(sub != list[j]);
            }
        }
        j = j + 1;
    }
    found
}
// </vc-code>

fn main() {
}

}