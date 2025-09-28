use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_subrange_identity(s: Seq<int>, i: int, j: int, k: int, l: int)
    requires
        0 <= i <= j <= s.len(),
        0 <= k <= l <= s.len(),
        s.subrange(i, j) =~= s.subrange(k, l),
    ensures
        i == k && j == l,
{
}

proof fn lemma_subrange_transitive(a: Seq<int>, b: Seq<int>, c: Seq<int>, i: int, j: int, k: int, l: int)
    requires
        0 <= i <= j <= a.len(),
        0 <= k <= l <= b.len(),
        a.subrange(i, j) =~= b.subrange(k, l),
        b.subrange(k, l) =~= c,
    ensures
        a.subrange(i, j) =~= c,
{
}

proof fn convert_usize_to_nat(x: usize) -> (y: nat)
    ensures
        y == x as nat,
{
    x as nat
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    let sub_len: usize = sub.len() as usize;
    let main_len: usize = main.len() as usize;
    
    if sub_len == 0 {
        return true;
    }
    
    if main_len < sub_len {
        return false;
    }
    
    let mut i: usize = 0;
    let upper_bound: usize = main_len - sub_len;
    
    while i <= upper_bound
        invariant
            0 <= i <= main_len,
            forall|k: usize| 0 <= k < i ==> {
                let k_int: int = k as int;
                !(sub =~= main.subrange(k_int, k_int + sub.len()))
            },
    {
        let mut j: usize = 0;
        let mut is_match = true;
        
        while j < sub_len
            invariant
                0 <= j <= sub_len,
                is_match == (forall|k: usize| 0 <= k < j ==> sub@[k as int] == main@[(i + k) as int]),
        {
            if sub@[j as int] != main@[(i + j) as int] {
                is_match = false;
                break;
            }
            j = j + 1;
        }
        
        if is_match {
            proof {
                let i_int: int = i as int;
                let sub_len_int: int = sub_len as int;
                assert(sub =~= main.subrange(i_int, i_int + sub_len_int));
            }
            return true;
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

fn main() {
}

}