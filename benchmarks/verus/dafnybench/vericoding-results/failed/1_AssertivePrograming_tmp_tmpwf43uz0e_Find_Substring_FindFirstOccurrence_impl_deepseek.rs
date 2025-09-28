use vstd::prelude::*;

verus! {

// Noa Leron 207131871
// Tsuri Farhana 315016907

spec fn is_prefix(prefix: Seq<char>, full: Seq<char>) -> bool {
    prefix.len() <= full.len() &&
    forall|k: int| 0 <= k < prefix.len() ==> prefix[k] == full[k]
}

spec fn exists_substring(str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|offset: int| 0 <= offset <= str1.len() - str2.len() &&
        is_prefix(str2, str1.subrange(offset, str1.len() as int))
}

spec fn post(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found <==> exists_substring(str1, str2)) &&
    (found ==> i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))
}

/*
Goal: Verify correctness of the following code. Once done, remove the {:verify false} (or turn it into {:verify true}).

Feel free to add GHOST code, including calls to lemmas. But DO NOT modify the specification or the original (executable) code.
*/

//this is our lemmas, invatiants and presicats

spec fn outter_inv_correctness(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found ==> (i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))) && // Second part of post condition
    (!found && 0 < i <= str1.len() && i != str2.len() - 1 ==> 
        !(exists_substring(str1.subrange(0, i as int), str2))) && // First part of post condition
    (!found ==> i <= str1.len())
}

spec fn inner_inv_correctness(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, found: bool) -> bool {
    0 <= j <= i && // index in range
    j < str2.len() && // index in range
    i < str1.len() && // index in range
    (str1[i as int] == str2[j] ==> 
        is_prefix(str2.subrange(j, str2.len() as int), str1.subrange(i as int, str1.len() as int))) &&
    (found ==> j == 0 && str1[i as int] == str2[j])
}

spec fn inner_inv_termination(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, old_i: nat, old_j: nat) -> bool {
    old_j - j == old_i - old_i
}

// <vc-helpers>
spec fn outer_inv(str1: Seq<char>, str2: Seq<char>, i: nat, found: bool) -> bool {
    i <= str1.len() &&
    (found ==> 
        i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int))) &&
    (!found ==> 
        forall|offset: int| 0 <= offset < i ==> 
            !is_prefix(str2, str1.subrange(offset, str1.len() as int)))
}

lemma proof_outer_inv_implies_post(str1: Seq<char>, str2: Seq<char>, i: nat, found: bool)
    requires
        outer_inv(str1, str2, i, found),
    ensures
        post(str1, str2, found, i)
{
}

lemma proof_is_prefix_empty(prefix: Seq<char>, full: Seq<char>)
    requires
        prefix.len() == 0,
    ensures
        is_prefix(prefix, full)
{
}

lemma proof_is_prefix_cons(c: char, prefix: Seq<char>, full: Seq<char>)
    requires
        prefix.len() + 1 <= full.len(),
        full[0] == c,
        is_prefix(prefix, full.subrange(1, full.len() as int)),
    ensures
        is_prefix(seq![c].add(prefix), full)
{
}

lemma proof_not_prefix_implies_skip(str1: Seq<char>, str2: Seq<char>, i: nat, j: int)
    requires
        0 <= j < str2.len(),
        i as int + j < str1.len() as int,
        str1[i as int + j] != str2[j],
    ensures
        forall|offset: int| i as int <= offset <= i as int + j ==> 
            !is_prefix(str2, str1.subrange(offset, str1.len() as int))
{
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut found: bool = false;
    
    while i <= str1.len() && !found
        invariant
            outer_inv(str1@, str2@, i as nat, found),
        decreases str1.len() - i,
    {
        if i + str2.len() > str1.len() {
            break;
        }
        
        let mut j: usize = 0;
        let mut matching: bool = true;
        
        while j < str2.len() && matching
            invariant
                0 <= j <= str2.len(),
                matching ==> j > 0 ==> forall|k: int| 0 <= k < j ==> str1@[i + k] == str2@[k],
                !matching ==> exists|k: int| 0 <= k < j && str1@[i + k] != str2@[k],
            decreases str2.len() - j,
        {
            if str1[i + j] != str2[j] {
                matching = false;
            } else {
                j = j + 1;
            }
        }
        
        if matching && j == str2.len() {
            found = true;
            proof_outer_inv_implies_post(str1@, str2@, i as nat, found);
        } else {
            proof {
                proof_not_prefix_implies_skip(str1@, str2@, i as nat, j as int);
            }
            i = i + 1;
        }
    }
    
    (found, i)
}
// </vc-code>

fn main() {
}

}