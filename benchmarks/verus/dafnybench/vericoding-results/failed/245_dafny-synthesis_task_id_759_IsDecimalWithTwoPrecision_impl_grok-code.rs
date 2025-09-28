use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
let tracked s_seq = s@;
let mut len_exec: usize = s.len();
let tracked len_spec = s_seq.len();
assert(len_exec as int == len_spec);
let tracked mut i_spec: int = 0;
let tracked mut has_matching: bool = false;
let mut i_exec: usize = 0;
while i_exec < len_exec
    invariant 0 <= i_spec == (i_exec as int) <= len_spec,
    invariant !has_matching ==> (forall #[trigger] i: nat where 0 <= i < i_spec ==> s_seq@[i] != '.' || len_spec - i - 1 != 2),
{
    let c = s.as_bytes()[i_exec];
    proof {
        assert(s_seq@[i_spec] == c as int);
    }
    if c == ('.' as u8) {
        if len_exec == i_exec + 3 {
            proof {
                assert(s_seq@[i_spec] == '.');
                assert(len_spec - i_spec - 1 == 2);
                assert(exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2);
                has_matching = true;
            }
            return true;
        } else {
        }
    }
    proof {
        if !has_matching {
            if c == ('.' as u8) {
                assert(s_seq@[i_spec] == '.' || len_spec - i_spec - 1 != 2);
            } else {
                assert(s_seq@[i_spec] != '.');
                assert(s_seq@[i_spec] != '.' || len_spec - i_spec - 1 != 2);
            }
        }
        i_spec = i_spec + 1;
    }
    i_exec = i_exec + 1;
}
proof {
    if !has_matching {
        assert(forall|i: nat| 0 <= i < len_spec ==> s_seq@[i] != '.' || len_spec - i - 1 != 2);
        assert(!exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2);
    }
}
false
}
// </vc-code>

fn main() {
}

}