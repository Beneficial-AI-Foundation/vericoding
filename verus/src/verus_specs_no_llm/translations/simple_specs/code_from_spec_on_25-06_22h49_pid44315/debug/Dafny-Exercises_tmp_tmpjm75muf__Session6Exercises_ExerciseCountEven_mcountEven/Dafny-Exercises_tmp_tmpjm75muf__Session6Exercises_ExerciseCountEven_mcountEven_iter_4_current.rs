use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn CountEven(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let rest_count = CountEven(s.subrange(1, s.len() as int));
        if first % 2 == 0 {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

// Helper lemma to prove the relationship between CountEven and subranges
proof fn lemma_count_even_extend(s: Seq<int>, i: int)
    requires
        0 <= i < s.len()
    ensures
        CountEven(s.subrange(0, i + 1)) == CountEven(s.subrange(0, i)) + (if s[i] % 2 == 0 { 1 } else { 0 })
    decreases s.len() - i
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    if i == 0 {
        assert(sub_i.len() == 0);
        assert(sub_i_plus_1.len() == 1);
        assert(sub_i_plus_1[0] == s[0]);
    } else {
        assert(sub_i_plus_1.len() > 0);
        assert(sub_i_plus_1[0] == s[0]);
        let rest_i = sub_i.subrange(1, sub_i.len() as int);
        let rest_i_plus_1 = sub_i_plus_1.subrange(1, sub_i_plus_1.len() as int);
        assert(rest_i =~= s.subrange(1, i));
        assert(rest_i_plus_1 =~= s.subrange(1, i + 1));
        lemma_count_even_extend(s.subrange(1, s.len() as int), i - 1);
    }
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires
        positive(v@)
    ensures
        n == CountEven(v@)
{
    let mut count = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            count == CountEven(v@.subrange(0, i as int)),
            positive(v@)
    {
        proof {
            lemma_count_even_extend(v@, i as int);
        }
        
        if v[i] % 2 == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(v@.subrange(0, v.len() as int) =~= v@);
    }
    
    count
}

}