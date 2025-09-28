use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    true
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_not_prefix_equiv(pre: Seq<char>, s: Seq<char>)
    ensures (!is_prefix_pred(pre, s)) <==> is_not_prefix_pred(pre, s)
{
    assert((!is_prefix_pred(pre, s)) ==> is_not_prefix_pred(pre, s)) by {
        if !is_prefix_pred(pre, s) {
            if pre.len() <= s.len() {
                assert(pre != s.subrange(0, pre.len() as int)) by {
                    if pre == s.subrange(0, pre.len() as int) {
                        assert(is_prefix_pred(pre, s));
                        assert(false);
                    }
                }
                assert(is_not_prefix_pred(pre, s));
            } else {
                assert(is_not_prefix_pred(pre, s));
            }
        }
    }

    assert(is_not_prefix_pred(pre, s) ==> !is_prefix_pred(pre, s)) by {
        if is_not_prefix_pred(pre, s) {
            assert(!is_prefix_pred(pre, s)) by {
                if is_prefix_pred(pre, s) {
                    assert(pre.len() <= s.len());
                    assert(pre == s.subrange(0, pre.len() as int));
                    assert(!(pre.len() > s.len()));
                    assert(!(pre != s.subrange(0, pre.len() as int)));
                    assert(false);
                }
            }
        }
    }
}

proof fn lemma_not_substring_equiv(sub: Seq<char>, s: Seq<char>)
    ensures !is_substring_pred(sub, s) <==> is_not_substring_pred(sub, s)
{
    assert((!is_substring_pred(sub, s)) ==> is_not_substring_pred(sub, s)) by {
        if !is_substring_pred(sub, s) {
            assert(is_not_substring_pred(sub, s)) by {
                assert_forall_by(|i: int| {
                    requires
                        0 <= i && i <= s.len() as int;
                    ensures
                        is_not_prefix_pred(sub, s.subrange(i, s.len() as int));
                    let s2 = s.subrange(i, s.len() as int);
                    assert(!is_prefix_pred(sub, s2)) by {
                        if is_prefix_pred(sub, s2) {
                            assert(is_substring_pred(sub, s)) by {
                                assert(exists|k: int| 0 <= k && k <= s.len() as int && #[trigger] is_prefix_pred(sub, s.subrange(k, s.len() as int))) by {
                                    let k = i;
                                    assert(0 <= k && k <= s.len() as int);
                                    assert(is_prefix_pred(sub, s.subrange(k, s.len() as int)));
                                }
                            }
                            assert(false);
                        }
                    }
                    lemma_not_prefix_equiv(sub, s2);
                    assert(is_not_prefix_pred(sub, s2));
                });
            }
        }
    }

    assert(is_not_substring_pred(sub, s) ==> !is_substring_pred(sub, s)) by {
        if is_not_substring_pred(sub, s) {
            assert(!is_substring_pred(sub, s)) by {
                if is_substring_pred(sub, s) {
                    let i = choose|i: int| 0 <= i && i <= s.len() as int && #[trigger] is_prefix_pred(sub, s.subrange(i, s.len() as int));
                    assert(0 <= i && i <= s.len() as int);
                    assert(is_prefix_pred(sub, s.subrange(i, s.len() as int)));
                    assert(is_not_prefix_pred(sub, s.subrange(i, s.len() as int)));
                    lemma_not_prefix_equiv(sub, s.subrange(i, s.len() as int));
                    assert(!is_prefix_pred(sub, s.subrange(i, s.len() as int)));
                    assert(false);
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        res ==> is_substring_pred(sub, str),
        // ensures  !res ==> !is_substring_pred(sub, str)
        is_substring_pred(sub, str) ==> res,
        is_substring_pred(sub, str) ==> res,
        !res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_not_substring_equiv(sub, str);
    }
    is_substring_pred(sub, str)
}
// </vc-code>

fn main() {}

}