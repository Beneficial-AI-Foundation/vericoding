use vstd::prelude::*;

verus! {

/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}



//(b)




//(c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}

// <vc-helpers>
proof fn prefix_sum_property(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len()
    ensures sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i >= j {
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == c[i] - c[i] == 0);
    } else {
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        prefix_sum_property(a, c, i + 1, j);
        assert(sum(a, i + 1, j) == c[j] - c[i + 1]);
        assert(c[i + 1] == c[i] + a[i]);
        assert(sum(a, i, j) == a[i] + (c[j] - c[i + 1]));
        assert(sum(a, i, j) == a[i] + c[j] - (c[i] + a[i]));
        assert(sum(a, i, j) == c[j] - c[i]);
    }
}

proof fn overflow_safe(a: &[i32], c: &[i32], i: i32, j: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures c@[j as int] as int - c@[i as int] as int >= i32::MIN as int,
        c@[j as int] as int - c@[i as int] as int <= i32::MAX as int
{
    let a_int = a@.map(|_i, x| x as int);
    let c_int = c@.map(|_i, x| x as int);
    
    assert(c@[i as int] >= i32::MIN && c@[i as int] <= i32::MAX);
    assert(c@[j as int] >= i32::MIN && c@[j as int] <= i32::MAX);
    
    let ci_val = c@[i as int] as int;
    let cj_val = c@[j as int] as int;
    
    assert(ci_val >= i32::MIN as int && ci_val <= i32::MAX as int);
    assert(cj_val >= i32::MIN as int && cj_val <= i32::MAX as int);
    
    let diff = cj_val - ci_val;
    
    assert(diff >= i32::MIN as int - i32::MAX as int);
    assert(diff <= i32::MAX as int - i32::MIN as int);
    
    assert(i32::MIN as int - i32::MAX as int >= i32::MIN as int);
    assert(i32::MAX as int - i32::MIN as int <= i32::MAX as int);
    
    assert(diff >= i32::MIN as int);
    assert(diff <= i32::MAX as int);
}
// </vc-helpers>

// <vc-spec>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    proof {
        let a_int = a@.map(|_i, x| x as int);
        let c_int = c@.map(|_i, x| x as int);
        prefix_sum_property(a_int, c_int, i as int, j as int);
        overflow_safe(a, c, i, j);
        
        assert(sum(a_int, i as int, j as int) == c_int[j as int] - c_int[i as int]);
        assert(c_int[j as int] == c@[j as int] as int);
        assert(c_int[i as int] == c@[i as int] as int);
        assert(c@[j as int] as int - c@[i as int] as int == c_int[j as int] - c_int[i as int]);
    }
    
    (c[j as usize] - c[i as usize])
}
// </vc-code>

fn main() {}

}