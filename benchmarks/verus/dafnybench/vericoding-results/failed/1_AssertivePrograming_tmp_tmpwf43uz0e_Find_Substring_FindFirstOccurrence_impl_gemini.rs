// <vc-preamble>
use vstd::prelude::*;

verus! {

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

spec fn outter_inv_correctness(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found ==> (i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))) &&
    (!found && 0 < i <= str1.len() && i != str2.len() - 1 ==> 
        !(exists_substring(str1.subrange(0, i as int), str2))) &&
    (!found ==> i <= str1.len())
}

spec fn inner_inv_correctness(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, found: bool) -> bool {
    0 <= j <= i &&
    j < str2.len() &&
    i < str1.len() &&
    (str1[i as int] == str2[j] ==> 
        is_prefix(str2.subrange(j, str2.len() as int), str1.subrange(i as int, str1.len() as int))) &&
    (found ==> j == 0 && str1[i as int] == str2[j])
}

spec fn inner_inv_termination(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, old_i: nat, old_j: nat) -> bool {
    old_j - j == old_i - old_i
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): cast .len() to int for subrange */
proof fn lemma_prefix_equality(s1: Seq<char>, s2: Seq<char>, offset: int)
    requires
        offset >= 0,
        offset + s2.len() <= s1.len(),
        forall|k: int| 0 <= k < s2.len() ==> s1[offset + k] == s2[k],
    ensures
        is_prefix(s2, s1.subrange(offset, s1.len() as int)),
{
    let sub = s1.subrange(offset, s1.len() as int);
    assert(s2.len() <= sub.len()) by {
        assert(sub.len() == s1.len() - offset);
    }
    assert forall|k: int| 0 <= k < s2.len() implies sub[k] == s2[k] by {
        assert(sub[k] == s1[offset + k]);
    }
    assert(is_prefix(s2, sub));
}

/* helper modified by LLM (iteration 3): cast .len() to int for subrange */
proof fn lemma_prefix_inequality(s1: Seq<char>, s2: Seq<char>, offset: int, k: int)
    requires
        offset >= 0,
        offset + s2.len() <= s1.len(),
        0 <= k < s2.len(),
        s1[offset + k] != s2[k],
    ensures
        !is_prefix(s2, s1.subrange(offset, s1.len() as int)),
{
    let sub = s1.subrange(offset, s1.len() as int);
    if is_prefix(s2, sub) {
        assert(s2[k] == sub[k]);
        assert(sub[k] == s1[offset + k]);
        assert(false);
    }
}

/* helper modified by LLM (iteration 3): cast .len() to int for subrange */
proof fn lemma_no_substring(str1: Seq<char>, str2: Seq<char>)
    requires
        str2.len() > 0,
        forall|i: int| 0 <= i <= str1.len() - str2.len() ==> !is_prefix(str2, str1.subrange(i, str1.len() as int)),
    ensures
        !exists_substring(str1, str2),
{
    assert forall|offset: int| 0 <= offset <= str1.len() - str2.len()
        implies !is_prefix(str2, str1.subrange(offset, str1.len() as int)) by {}
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fix all compilation errors (type casts) */
{
    let str1_len = str1.len();
    let str2_len = str2.len();

    if str2_len == 0 as nat {
        proof {
            assert(is_prefix(str2, str1.subrange(0, str1.len() as int)));
            assert(exists_substring(str1, str2));
        }
        return (true, 0);
    }
    
    if str1_len < str2_len {
        proof {
            assert(str1.len() - str2.len() < 0);
            assert forall|offset: int| 0 <= offset <= str1.len() - str2.len()
                implies false by {}
            assert(!exists_substring(str1, str2));
        }
        return (false, 0);
    }

    let str1_len_usize = str1_len as u64 as usize;
    let str2_len_usize = str2_len as u64 as usize;

    let mut i: usize = 0;
    while i <= str1_len_usize - str2_len_usize
        invariant
            0 <= i as nat <= str1.len() - str2.len() + 1,
            str2.len() > 0,
            forall|k: int| 0 <= k < i as int ==> !is_prefix(str2, str1.subrange(k, str1.len() as int)),
        decreases str1.len() - (i as nat)
    {
        let mut j: usize = 0;
        let mut is_match = true;

        while j < str2_len_usize
            invariant
                0 <= j as nat <= str2.len(),
                is_match <==> (forall|k: int| 0 <= k < j as int ==> str1[i as int + k] == str2[k]),
                i as nat + str2.len() <= str1.len(),
            decreases str2.len() - (j as nat)
        {
            let ne = proof { str1[i as int + j as int] != str2[j as int] };
            if ne {
                is_match = false;
                proof { lemma_prefix_inequality(str1, str2, i as int, j as int); }
                break;
            }
            j = j + 1;
        }

        if is_match {
            proof {
                assert(j as nat == str2.len());
                assert forall|k: int| 0 <= k < str2.len() ==> str1[i as int + k] == str2[k] by {
                    assert(is_match);
                }
                lemma_prefix_equality(str1, str2, i as int);
                assert(exists_substring(str1, str2));
            }
            return (true, i);
        }
        i = i + 1;
    }

    proof {
        assert(i as nat == str1.len() - str2.len() + 1);
        assert forall|k: int| 0 <= k <= str1.len() - str2.len()
            implies !is_prefix(str2, str1.subrange(k, str1.len() as int)) by {}
        lemma_no_substring(str1, str2);
        assert(!exists_substring(str1, str2));
    }
    return (false, 0);
}
// </vc-code>

}
fn main() {}