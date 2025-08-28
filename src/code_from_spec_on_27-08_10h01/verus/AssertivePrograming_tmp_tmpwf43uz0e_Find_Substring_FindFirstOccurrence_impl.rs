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
proof fn lemma_prefix_transitive(s1: Seq<char>, s2: Seq<char>, s3: Seq<char>)
    requires 
        is_prefix(s1, s2),
        is_prefix(s2, s3)
    ensures is_prefix(s1, s3)
{
}

proof fn lemma_subrange_prefix(s: Seq<char>, start: int, end: int, prefix: Seq<char>)
    requires 
        0 <= start <= end <= s.len(),
        is_prefix(prefix, s.subrange(start, end))
    ensures is_prefix(prefix, s.subrange(start, s.len() as int))
{
}

proof fn lemma_exists_substring_offset(str1: Seq<char>, str2: Seq<char>, offset: int)
    requires 
        0 <= offset <= str1.len() - str2.len(),
        is_prefix(str2, str1.subrange(offset, str1.len() as int))
    ensures exists_substring(str1, str2)
{
}

proof fn lemma_no_substring_in_prefix(str1: Seq<char>, str2: Seq<char>, i: int)
    requires 
        0 <= i <= str1.len(),
        str2.len() > 0,
        forall|k: int| 0 <= k < i ==> !is_prefix(str2, str1.subrange(k, str1.len() as int))
    ensures !exists_substring(str1.subrange(0, i), str2)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if str2.len() == 0nat {
        return (true, 0);
    }
    
    if str1.len() < str2.len() {
        return (false, 0);
    }
    
    let mut i: usize = 0;
    let mut found = false;
    
    while i <= (str1.len() - str2.len()) as usize && !found
        invariant 
            i <= str1.len() as usize,
            outter_inv_correctness(str1, str2, found, i as nat),
            !found ==> forall|k: int| 0 <= k < i ==> !is_prefix(str2, str1.subrange(k, str1.len() as int))
        decreases str1.len() - i as nat
    {
        let mut j: usize = 0;
        let old_i = i;
        
        while j < str2.len() as usize && i < str1.len() as usize && str1@[i] == str2@[j]
            invariant
                0 <= j <= str2.len() as usize,
                i == old_i + j,
                i <= str1.len() as usize,
                j > 0 ==> is_prefix(str2.subrange(0, j as int), str1.subrange(old_i as int, str1.len() as int))
            decreases str2.len() - j as nat
        {
            i += 1;
            j += 1;
        }
        
        if j == str2.len() as usize {
            found = true;
            i = old_i;
            proof {
                lemma_exists_substring_offset(str1, str2, old_i as int);
            }
        } else {
            i = old_i + 1;
        }
    }
    
    if found {
        (true, i)
    } else {
        (false, 0)
    }
}
// </vc-code>

fn main() {
}

}