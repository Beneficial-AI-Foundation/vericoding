use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Max(s: Seq<int>) -> int
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = Max(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
    }
}

spec fn Min(s: Seq<int>) -> int
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = Min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn lemma_max_in_range(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 <= i < s.len()
    ensures
        Max(s) >= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(i == 0);
        assert(Max(s) == s[0]);
    } else {
        let rest = s.subrange(1, s.len() as int);
        if i == 0 {
            // s[0] is compared with Max(rest) in the definition
        } else {
            // s[i] is in the rest
            assert(s[i] == rest[i - 1]);
            lemma_max_in_range(rest, i - 1);
            assert(Max(rest) >= s[i]);
        }
    }
}

proof fn lemma_min_in_range(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 <= i < s.len()
    ensures
        Min(s) <= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(i == 0);
        assert(Min(s) == s[0]);
    } else {
        let rest = s.subrange(1, s.len() as int);
        if i == 0 {
            // s[0] is compared with Min(rest) in the definition
        } else {
            // s[i] is in the rest
            assert(s[i] == rest[i - 1]);
            lemma_min_in_range(rest, i - 1);
            assert(Min(rest) <= s[i]);
        }
    }
}

proof fn lemma_max_update(s: Seq<int>, current_max: int, i: int)
    requires
        s.len() > 0,
        0 < i < s.len(),
        current_max == Max(s.subrange(0, i as int))
    ensures
        Max(s.subrange(0, (i + 1) as int)) == if s[i] > current_max { s[i] } else { current_max }
    decreases s.len() - i
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    // Show that prefix_i_plus_1 = prefix_i.push(s[i])
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    assert(prefix_i_plus_1[i] == s[i]);
    
    // Use the definition of Max on prefix_i_plus_1
    if prefix_i_plus_1.len() == 1 {
        assert(i == 0); // contradiction since i > 0
    } else {
        let rest = prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int);
        assert(rest =~= prefix_i);
        assert(Max(prefix_i_plus_1) == if prefix_i_plus_1[0] >= Max(rest) { prefix_i_plus_1[0] } else { Max(rest) });
        assert(prefix_i_plus_1[0] == s[0]);
        assert(Max(rest) == Max(prefix_i));
    }
    
    lemma_max_in_range(prefix_i_plus_1, 0);
    lemma_max_in_range(prefix_i_plus_1, i);
}

proof fn lemma_min_update(s: Seq<int>, current_min: int, i: int)
    requires
        s.len() > 0,
        0 < i < s.len(),
        current_min == Min(s.subrange(0, i as int))
    ensures
        Min(s.subrange(0, (i + 1) as int)) == if s[i] < current_min { s[i] } else { current_min }
    decreases s.len() - i
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    // Show that prefix_i_plus_1 = prefix_i.push(s[i])
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    assert(prefix_i_plus_1[i] == s[i]);
    
    // Use the definition of Min on prefix_i_plus_1
    if prefix_i_plus_1.len() == 1 {
        assert(i == 0); // contradiction since i > 0
    } else {
        let rest = prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int);
        assert(rest =~= prefix_i);
        assert(Min(prefix_i_plus_1) == if prefix_i_plus_1[0] <= Min(rest) { prefix_i_plus_1[0] } else { Min(rest) });
        assert(prefix_i_plus_1[0] == s[0]);
        assert(Min(rest) == Min(prefix_i));
    }
    
    lemma_min_in_range(prefix_i_plus_1, 0);
    lemma_min_in_range(prefix_i_plus_1, i);
}

fn DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 0
    ensures
        diff == (Max(a@) - Min(a@))
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        proof {
            lemma_max_update(a@, max_val, i as int);
            lemma_min_update(a@, min_val, i as int);
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        i += 1;
    }
    
    // At the end, i == a.len(), so we have the full sequence
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}