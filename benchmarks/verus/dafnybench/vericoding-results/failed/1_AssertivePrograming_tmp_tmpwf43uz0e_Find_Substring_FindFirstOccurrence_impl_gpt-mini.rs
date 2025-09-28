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
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
{
    let n1: nat = str1.len();
    let n2: nat = str2.len();
    if n2 > n1 {
        return (false, 0usize);
    }
    let max_i: nat = n1 - n2; // maximum starting index for a match
    let mut i: nat = 0;
    while i <= max_i
        invariant i <= max_i + 1;
        invariant forall|k: int| 0 <= k && k < (i as int) ==> !is_prefix(str2, str1.subrange(k, n1 as int));
        decreases (max_i + 1) - i;
    {
        // try to match at position i
        let mut j: nat = 0;
        let mut ok: bool = true;
        while j < n2 && ok
            invariant j <= n2;
            invariant forall|t: int| 0 <= t && t < (j as int) ==> str1[(i as int) + t] == str2[t];
            invariant (i + j) <= n1;
            decreases n2 - j;
        {
            if str1[(i + j) as int] != str2[(j as int)] {
                ok = false;
            } else {
                j = j + 1;
            }
        }
        if ok {
            // full match found at i: j == n2 and forall t < n2, equalities hold
            proof {
                assert(j == n2);
                // from i <= max_i and max_i = n1 - n2, get i + n2 <= n1
                assert(i <= max_i);
                assert((i + n2) <= n1);
                assert(forall|k: int| 0 <= k < (n2 as int) ==> str2[k] == str1[(i as int) + k]);
                assert(is_prefix(str2, str1.subrange(i as int, n1 as int)));
            }
            return (true, i as usize);
        } else {
            // we have a concrete mismatch at some index j < n2, so not a prefix at i
            proof {
                assert(j <= n2);
                assert(j < n2);
                let k0: int = j as int;
                assert(0 <= k0 && k0 < (n2 as int));
                assert(str1[(i as int) + k0] != str2[k0]);
                assert(!is_prefix(str2, str1.subrange(i as int, n1 as int)));
            }
            i = i + 1;
        }
    }
    // scanned all possible offsets without finding a match
    proof {
        assert(i == max_i + 1);
        assert(forall|k: int| 0 <= k < (i as int) ==> !is_prefix(str2, str1.subrange(k, n1 as int)));
        assert(!exists|offset: int| 0 <= offset && offset <= max_i as int && is_prefix(str2, str1.subrange(offset, n1 as int)));
        assert(!exists|offset: int| 0 <= offset <= (n1 as int) - (n2 as int) && is_prefix(str2, str1.subrange(offset, n1 as int)));
    }
    (false, 0usize)
}
// </vc-code>

fn main() {
}

}