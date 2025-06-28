use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0 <= j < k < u.len() ==> u.spec_index(j) != u.spec_index(k)
}

spec fn bullspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    let mut count = 0;
    for i in 0..s.len() {
        if s.spec_index(i) == u.spec_index(i) {
            count = count + 1;
        }
    }
    count
}

spec fn cowspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    let mut count = 0;
    for i in 0..s.len() {
        if s.spec_index(i) != u.spec_index(i) {
            for j in 0..u.len() {
                if s.spec_index(i) == u.spec_index(j) {
                    count = count + 1;
                    break;
                }
            }
        }
    }
    count
}

fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat) 
    requires 
        0 < s.len() == u.len() <= 10,
        nomultiples(u) && nomultiples(s)
    ensures 
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
{
    let mut b: nat = 0;
    let mut c: nat = 0;
    
    // Count bulls (exact position matches)
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            b >= 0
    {
        if s.spec_index(i) == u.spec_index(i) {
            b = b + 1;
        }
        i = i + 1;
    }
    
    // Count cows (digit exists but wrong position)
    i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            c >= 0
    {
        if s.spec_index(i) != u.spec_index(i) {
            let mut j = 0;
            while j < u.len()
                invariant 0 <= j <= u.len()
            {
                if s.spec_index(i) == u.spec_index(j) {
                    c = c + 1;
                    break;
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    
    (b, c)
}

}