// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_sf_flights(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 { 
        0 
    } else { 
        (if s[s.len()-1] == 'F' && s[s.len()-2] != 'F' { 1int } else { 0int }) + count_sf_flights(s.subrange(0, s.len()-1))
    }
}

spec fn count_fs_flights(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 { 
        0 
    } else { 
        (if s[s.len()-1] == 'S' && s[s.len()-2] != 'S' { 1int } else { 0int }) + count_fs_flights(s.subrange(0, s.len()-1))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed index correspondence in lemmas */
proof fn count_sf_flights_extend(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        i >= 1,
    ensures
        count_sf_flights(s.subrange(0, i + 1)) == 
        count_sf_flights(s.subrange(0, i)) + 
        (if s[i] == 'F' && s[i-1] != 'F' { 1int } else { 0int })
    decreases s.len() - i
{
    let sub = s.subrange(0, i + 1);
    if sub.len() <= 1 {
        assert(count_sf_flights(sub) == 0);
        assert(i == 0);
    } else {
        assert(sub.len() == i + 1);
        assert(sub[sub.len()-1] == s[i]);
        assert(sub[sub.len()-2] == s[i-1]);
        assert(sub.subrange(0, sub.len()-1) == s.subrange(0, i));
        assert(count_sf_flights(sub) == 
            (if sub[sub.len()-1] == 'F' && sub[sub.len()-2] != 'F' { 1int } else { 0int }) + 
            count_sf_flights(sub.subrange(0, sub.len()-1)));
    }
}

proof fn count_fs_flights_extend(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        i >= 1,
    ensures
        count_fs_flights(s.subrange(0, i + 1)) == 
        count_fs_flights(s.subrange(0, i)) + 
        (if s[i] == 'S' && s[i-1] != 'S' { 1int } else { 0int })
    decreases s.len() - i
{
    let sub = s.subrange(0, i + 1);
    if sub.len() <= 1 {
        assert(count_fs_flights(sub) == 0);
        assert(i == 0);
    } else {
        assert(sub.len() == i + 1);
        assert(sub[sub.len()-1] == s[i]);
        assert(sub[sub.len()-2] == s[i-1]);
        assert(sub.subrange(0, sub.len()-1) == s.subrange(0, i));
        assert(count_fs_flights(sub) == 
            (if sub[sub.len()-1] == 'S' && sub[sub.len()-2] != 'S' { 1int } else { 0int }) + 
            count_fs_flights(sub.subrange(0, sub.len()-1)));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 2,
        s@.len() == n,
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'S' || s@[i] == 'F',
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> count_sf_flights(s@) > count_fs_flights(s@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes to code, only helpers needed fixing */
    let mut sf_count: usize = 0;
    let mut fs_count: usize = 0;
    let mut i: usize = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            n == s@.len(),
            sf_count <= i,
            fs_count <= i,
            sf_count == count_sf_flights(s@.subrange(0, i as int)),
            fs_count == count_fs_flights(s@.subrange(0, i as int)),
        decreases n - i
    {
        let old_sf = sf_count;
        let old_fs = fs_count;
        
        proof {
            count_sf_flights_extend(s@, i as int);
            count_fs_flights_extend(s@, i as int);
        }
        
        if s[i] == 'F' && s[i-1] != 'F' {
            sf_count = sf_count + 1;
        }
        if s[i] == 'S' && s[i-1] != 'S' {
            fs_count = fs_count + 1;
        }
        
        i = i + 1;
    }
    
    assert(s@.subrange(0, n as int) == s@);
    
    if sf_count > fs_count {
        vec!['Y', 'E', 'S']
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}