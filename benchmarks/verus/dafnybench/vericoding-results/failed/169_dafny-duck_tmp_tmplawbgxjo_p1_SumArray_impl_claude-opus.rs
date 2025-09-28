use vstd::prelude::*;

verus! {

// Given an array of integers, it returns the sum. [1,3,3,2]->9

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

// <vc-helpers>
proof fn sum_prop(xs: Seq<i32>, i: int)
    requires 0 <= i < xs.len()
    ensures sum(xs.subrange(0, i)) + xs[i] as int == sum(xs.subrange(0, i + 1))
    decreases xs.len() - i
{
    let s1 = xs.subrange(0, i + 1);
    assert(0 <= 0 <= i + 1 <= xs.len());
    assert(s1.len() == i + 1);
    
    if i == 0 {
        assert(s1.len() == 1);
        assert(sum(xs.subrange(0, 0)) == 0);
        assert(s1 =~= xs.subrange(0, 1));
        assert(sum(s1) == sum(xs.subrange(0, 0)) + s1[s1.len() - 1] as int);
        assert(s1[0] == xs[0]);
    } else {
        assert(i >= 1);
        assert(s1.len() >= 1);
        assert(0 <= i < xs.len());
        assert(s1.subrange(0, s1.len() - 1) =~= xs.subrange(0, i));
        assert(s1[s1.len() - 1] == xs[i]);
        assert(sum(s1) == sum(s1.subrange(0, s1.len() - 1)) + s1[s1.len() - 1] as int);
        assert(sum(s1) == sum(xs.subrange(0, i)) + xs[i] as int);
    }
}

proof fn sum_empty()
    ensures sum(Seq::<i32>::empty()) == 0
{
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            s as int == sum(xs@.subrange(0, i as int)),
            s >= i32::MIN,
            s <= i32::MAX,
        decreases xs.len() - i
    {
        let old_s = s;
        let old_i = i;
        
        proof {
            assert(0 <= i < xs.len());
            sum_prop(xs@, i as int);
            assert(sum(xs@.subrange(0, i as int)) + xs@[i as int] as int == sum(xs@.subrange(0, (i + 1) as int)));
        }
        
        if xs[i] > 0 && s > i32::MAX - xs[i] {
            // Would overflow
            return s;
        } else if xs[i] < 0 && s < i32::MIN - xs[i] {
            // Would underflow  
            return s;
        }
        
        s = s + xs[i];
        i = i + 1;
        
        proof {
            assert(i == old_i + 1);
            assert(s as int == old_s as int + xs@[old_i as int] as int);
            assert(old_s as int == sum(xs@.subrange(0, old_i as int)));
            assert(s as int == sum(xs@.subrange(0, old_i as int)) + xs@[old_i as int] as int);
            assert(s as int == sum(xs@.subrange(0, i as int)));
        }
    }
    
    proof {
        assert(i == xs.len());
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    
    s
}
// </vc-code>

fn main() {
}

}