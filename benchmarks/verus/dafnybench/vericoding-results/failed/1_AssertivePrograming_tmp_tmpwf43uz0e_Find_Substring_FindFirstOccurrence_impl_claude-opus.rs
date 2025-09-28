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
proof fn lemma_no_substring_in_extended_range(str1: Seq<char>, str2: Seq<char>, i: usize)
    requires
        i < str1.len(),
        str2.len() > 0,
        !exists_substring(str1.subrange(0, i as int), str2),
        !is_prefix(str2, str1.subrange(i as int, str1.len() as int)),
    ensures
        !exists_substring(str1.subrange(0, (i + 1) as int), str2),
{
    if exists_substring(str1.subrange(0, (i + 1) as int), str2) {
        let offset = choose|offset: int| 
            0 <= offset <= (i + 1) as int - str2.len() as int &&
            is_prefix(str2, str1.subrange(0, (i + 1) as int).subrange(offset, (i + 1) as int));
        
        if offset < i as int {
            assert(offset <= i as int - str2.len() as int);
            assert(str1.subrange(0, i as int).subrange(offset, i as int) =~= 
                   str1.subrange(offset, i as int));
            assert(str1.subrange(0, (i + 1) as int).subrange(offset, (i + 1) as int) =~=
                   str1.subrange(offset, (i + 1) as int));
            assert(forall|k: int| 0 <= k < str2.len() ==> 
                   str1.subrange(offset, (i + 1) as int)[k] == str1[offset + k]);
            assert(forall|k: int| 0 <= k < str2.len() ==> 
                   str1.subrange(offset, i as int)[k] == str1[offset + k]);
            assert(is_prefix(str2, str1.subrange(offset, i as int)));
            assert(exists_substring(str1.subrange(0, i as int), str2));
            assert(false);
        } else {
            assert(offset == i as int);
            assert(str1.subrange(0, (i + 1) as int).subrange(i as int, (i + 1) as int) =~=
                   str1.subrange(i as int, (i + 1) as int));
            assert(is_prefix(str2, str1.subrange(i as int, (i + 1) as int)));
            assert(str1.subrange(i as int, (i + 1) as int).len() >= str1.subrange(i as int, str1.len() as int).len());
            assert(is_prefix(str2, str1.subrange(i as int, str1.len() as int)));
            assert(false);
        }
    }
}

proof fn lemma_substring_exists_at_offset(str1: Seq<char>, str2: Seq<char>, i: usize)
    requires
        i as nat + str2.len() <= str1.len(),
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)),
    ensures
        exists_substring(str1, str2),
{
    assert(str1.subrange(i as int, str1.len() as int).len() >= str2.len());
    assert(forall|k: int| 0 <= k < str2.len() ==> 
           str2[k] == str1.subrange(i as int, str1.len() as int)[k]);
    assert(is_prefix(str2, str1.subrange(i as int, str1.len() as int)));
    assert(exists_substring(str1, str2));
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
{
    if str2.len() == 0 {
        return (true, 0);
    }
    
    if str1.len() < str2.len() {
        assert(!exists_substring(str1, str2)) by {
            if exists_substring(str1, str2) {
                let offset = choose|offset: int| 
                    0 <= offset <= str1.len() - str2.len() &&
                    is_prefix(str2, str1.subrange(offset, str1.len() as int));
                assert(offset <= str1.len() - str2.len());
                assert(str1.len() < str2.len());
                assert(false);
            }
        }
        return (false, 0);
    }
    
    let mut i: usize = 0;
    let mut found = false;
    
    while i <= str1.len() - str2.len()
        invariant
            i <= str1.len() - str2.len() + 1,
            found ==> i < str1.len() - str2.len() + 1,
            found ==> is_prefix(str2, str1.subrange(i as int, str1.len() as int)),
            !found ==> !exists_substring(str1.subrange(0, i as int), str2),
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < str2.len()
            invariant
                j <= str2.len(),
                matches ==> forall|k: int| 0 <= k < j as int ==> str1[i as int + k] == str2[k],
                !matches ==> !is_prefix(str2, str1.subrange(i as int, str1.len() as int)),
        {
            let idx1 = i + j;
            let idx2 = j;
            if str1[idx1] != str2[idx2] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            assert(j == str2.len());
            assert(forall|k: int| 0 <= k < str2.len() ==> str1[i as int + k] == str2[k]);
            assert(forall|k: int| 0 <= k < str2.len() ==> 
                   str1.subrange(i as int, str1.len() as int)[k] == str2[k]);
            assert(is_prefix(str2, str1.subrange(i as int, str1.len() as int)));
            found = true;
            break;
        } else {
            proof {
                lemma_no_substring_in_extended_range(str1, str2, i);
            }
        }
        
        i = i + 1;
    }
    
    if found {
        proof {
            lemma_substring_exists_at_offset(str1, str2, i);
        }
        return (true, i);
    } else {
        assert(i == str1.len() - str2.len() + 1);
        assert(!exists_substring(str1.subrange(0, i as int), str2));
        assert(str1.subrange(0, str1.len() as int) =~= str1);
        assert(!exists_substring(str1, str2));
        return (false, 0);
    }
}
// </vc-code>

fn main() {
}

}