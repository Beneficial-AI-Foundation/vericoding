use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = Max(s.subrange(1, s.len() as int));
        if s[0] > rest_max { s[0] } else { rest_max }
    }
}

spec fn Min(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = Min(s.subrange(1, s.len() as int));
        if s[0] < rest_min { s[0] } else { rest_min }
    }
}

// Helper lemma for Max properties
proof fn lemma_max_properties(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] <= Max(s)
    decreases s.len()
{
    if s.len() == 1 {
        // Base case is trivial
        assert(s[0] == Max(s));
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_max_properties(rest);
        
        let max_rest = Max(rest);
        let max_s = Max(s);
        
        // By definition: max_s = if s[0] > max_rest { s[0] } else { max_rest }
        if s[0] > max_rest {
            assert(max_s == s[0]);
            assert(s[0] <= max_s);
            // All elements in rest are <= max_rest < s[0] = max_s
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] == rest[(i-1) as int]);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= max_rest);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] < max_s);
        } else {
            assert(max_s == max_rest);
            assert(s[0] <= max_rest);
            assert(s[0] <= max_s);
            // All elements in rest are <= max_rest = max_s
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] == rest[(i-1) as int]);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= max_s);
        }
    }
}

// Helper lemma for Min properties  
proof fn lemma_min_properties(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] >= Min(s)
    decreases s.len()
{
    if s.len() == 1 {
        // Base case is trivial
        assert(s[0] == Min(s));
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_min_properties(rest);
        
        let min_rest = Min(rest);
        let min_s = Min(s);
        
        // By definition: min_s = if s[0] < min_rest { s[0] } else { min_rest }
        if s[0] < min_rest {
            assert(min_s == s[0]);
            assert(s[0] >= min_s);
            // All elements in rest are >= min_rest > s[0] = min_s
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] == rest[(i-1) as int]);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= min_rest);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] > min_s);
        } else {
            assert(min_s == min_rest);
            assert(s[0] >= min_rest);
            assert(s[0] >= min_s);
            // All elements in rest are >= min_rest = min_s
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] == rest[(i-1) as int]);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] >= min_s);
        }
    }
}

// Lemma about extending sequences for Max
proof fn lemma_max_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Max(s.push(x)) == if x > Max(s) { x } else { Max(s) }
    decreases s.len()
{
    let extended = s.push(x);
    if s.len() == 1 {
        // Base case: s has one element
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        let rest_of_extended = extended.subrange(1, 2 as int);
        assert(rest_of_extended.len() == 1);
        assert(rest_of_extended[0] == x);
        assert(Max(rest_of_extended) == x);
        assert(Max(s) == s[0]);
        
        let max_extended = Max(extended);
        // By definition: max_extended = if s[0] > x { s[0] } else { x }
        if s[0] > x {
            assert(max_extended == s[0]);
            assert(max_extended == Max(s));
            assert(!(x > Max(s)));
        } else {
            assert(max_extended == x);
            assert(x >= s[0]);
            assert(x >= Max(s));
        }
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        // Show that extended_rest is s_rest.push(x)
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest =~= s_rest.push(x));
        
        lemma_max_extend(s_rest, x);
        
        let max_s_rest = Max(s_rest);
        let max_extended_rest = Max(extended_rest);
        let max_s = Max(s);
        let max_extended = Max(extended);
        
        // From the inductive hypothesis
        assert(max_extended_rest == if x > max_s_rest { x } else { max_s_rest });
        
        // From the definitions
        assert(max_s == if s[0] > max_s_rest { s[0] } else { max_s_rest });
        assert(max_extended == if s[0] > max_extended_rest { s[0] } else { max_extended_rest });
        
        // Case analysis to show the final result
        if x > Max(s) {
            // We need to show max_extended == x
            if x > max_s_rest {
                assert(max_extended_rest == x);
                if s[0] > x {
                    // This contradicts x > Max(s) since Max(s) >= s[0]
                    assert(max_s >= s[0]);
                    assert(false);
                } else {
                    assert(max_extended == max_extended_rest);
                    assert(max_extended == x);
                }
            } else {
                // x <= max_s_rest, but x > Max(s)
                // This means Max(s) = s[0] and s[0] < x <= max_s_rest
                assert(max_s == s[0]);
                assert(s[0] > max_s_rest);
                assert(false); // Contradiction
            }
        } else {
            // x <= Max(s), we need to show max_extended == Max(s)
            if x > max_s_rest {
                assert(max_extended_rest == x);
                if s[0] > x {
                    assert(max_extended == s[0]);
                    assert(max_s >= s[0]); // Since Max(s) is max of s[0] and max_s_rest
                    if max_s == s[0] {
                        assert(max_extended == max_s);
                    } else {
                        assert(max_s == max_s_rest);
                        assert(s[0] <= max_s_rest);
                        assert(false); // Contradiction with s[0] > x > max_s_rest
                    }
                } else {
                    assert(max_extended == max_extended_rest);
                    assert(max_extended == x);
                    assert(x <= max_s);
                    assert(max_extended == max_s);
                }
            } else {
                assert(max_extended_rest == max_s_rest);
                assert(max_extended == if s[0] > max_s_rest { s[0] } else { max_s_rest });
                assert(max_extended == max_s);
            }
        }
    }
}

// Lemma about extending sequences for Min
proof fn lemma_min_extend(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures 
        s.push(x).len() > 0,
        Min(s.push(x)) == if x < Min(s) { x } else { Min(s) }
    decreases s.len()
{
    let extended = s.push(x);
    if s.len() == 1 {
        // Base case: s has one element
        assert(extended.len() == 2);
        assert(extended[0] == s[0]);
        assert(extended[1] == x);
        let rest_of_extended = extended.subrange(1, 2 as int);
        assert(rest_of_extended.len() == 1);
        assert(rest_of_extended[0] == x);
        assert(Min(rest_of_extended) == x);
        assert(Min(s) == s[0]);
        
        let min_extended = Min(extended);
        // By definition: min_extended = if s[0] < x { s[0] } else { x }
        if s[0] < x {
            assert(min_extended == s[0]);
            assert(min_extended == Min(s));
            assert(!(x < Min(s)));
        } else {
            assert(min_extended == x);
            assert(x <= s[0]);
            assert(x <= Min(s));
        }
    } else {
        // Inductive case
        let s_rest = s.subrange(1, s.len() as int);
        let extended_rest = extended.subrange(1, extended.len() as int);
        
        // Show that extended_rest is s_rest.push(x)
        assert(extended_rest.len() == s_rest.len() + 1);
        assert(forall|i: int| 0 <= i < s_rest.len() ==> extended_rest[i] == s_rest[i]);
        assert(extended_rest[s_rest.len() as int] == x);
        assert(extended_rest =~= s_rest.push(x));
        
        lemma_min_extend(s_rest, x);
        
        let min_s_rest = Min(s_rest);
        let min_extended_rest = Min(extended_rest);
        let min_s = Min(s);
        let min_extended = Min(extended);
        
        // From the inductive hypothesis
        assert(min_extended_rest == if x < min_s_rest { x } else { min_s_rest });
        
        // From the definitions
        assert(min_s == if s[0] < min_s_rest { s[0] } else { min_s_rest });
        assert(min_extended == if s[0] < min_extended_rest { s[0] } else { min_extended_rest });
        
        // Case analysis to show the final result
        if x < Min(s) {
            // We need to show min_extended == x
            if x < min_s_rest {
                assert(min_extended_rest == x);
                if s[0] < x {
                    // This contradicts x < Min(s) since Min(s) <= s[0]
                    assert(min_s <= s[0]);
                    assert(false);
                } else {
                    assert(min_extended == min_extended_rest);
                    assert(min_extended == x);
                }
            } else {
                // x >= min_s_rest, but x < Min(s)
                // This means Min(s) = s[0] and s[0] > x >= min_s_rest
                assert(min_s == s[0]);
                assert(s[0] < min_s_rest);
                assert(false); // Contradiction
            }
        } else {
            // x >= Min(s), we need to show min_extended == Min(s)
            if x < min_s_rest {
                assert(min_extended_rest == x);
                if s[0] < x {
                    assert(min_extended == s[0]);
                    assert(min_s <= s[0]); // Since Min(s) is min of s[0] and min_s_rest
                    if min_s == s[0] {
                        assert(min_extended == min_s);
                    } else {
                        assert(min_s == min_s_rest);
                        assert(s[0] >= min_s_rest);
                        assert(false); // Contradiction with s[0] < x < min_s_rest
                    }
                } else {
                    assert(min_extended == min_extended_rest);
                    assert(min_extended == x);
                    assert(x >= min_s);
                    assert(min_extended == min_s);
                }
            } else {
                assert(min_extended_rest == min_s_rest);
                assert(min_extended == if s[0] < min_s_rest { s[0] } else { min_s_rest });
                assert(min_extended == min_s);
            }
        }
    }
}

fn SumMinMax(a: Vec<int>) -> (sum: int)
    requires
        a.len() > 0
    ensures
        sum == Max(a@) + Min(a@)
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    // Base case: when i = 1, we have processed element 0
    assert(a@.subrange(0, 1).len() == 1);
    assert(a@.subrange(0, 1)[0] == a[0]);
    assert(Max(a@.subrange(0, 1)) == a[0]);
    assert(Min(a@.subrange(0, 1)) == a[0]);
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a@.subrange(0, i as int).len() > 0,
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        let current_seq = a@.subrange(0, i as int);
        let next_seq = a@.subrange(0, (i + 1) as int);
        
        // Establish that next_seq is current_seq.push(a[i])
        assert(next_seq.len() == current_seq.len() + 1);
        assert(forall|j: int| 0 <= j < current_seq.len() ==> next_seq[j] == current_seq[j]);
        assert(next_seq[current_seq.len() as int] == a[i as int]);
        assert(next_seq =~= current_seq.push(a[i as int]));
        
        // Apply our lemmas
        proof {
            lemma_max_extend(current_seq, a[i as int]);
            lemma_min_extend(current_seq, a[i as int]);
        }
        
        // Update values based on the lemmas
        if a[i] > max_val {
            max_val = a[i];
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        
        // The lemmas tell us what the new max and min should be
        assert(max_val == (if a[i as int] > Max(current_seq) { a[i as int] } else { Max(current_seq) }));
        assert(min_val == (if a[i as int] < Min(current_seq) { a[i as int] } else { Min(current_seq) }));
        assert(max_val == Max(next_seq));
        assert(min_val == Min(next_seq));
        
        i += 1;
    }
    
    // At loop exit, we have processed all elements
    assert(i == a.len());
    assert(a@.subrange(0, a.len() as int) =~= a@);
    assert(max_val == Max(a@));
    assert(min_val == Min(a@));
    
    max_val + min_val
}

}