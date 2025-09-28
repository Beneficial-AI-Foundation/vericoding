// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sumc(s: Seq<int>, p: Seq<bool>) -> int
    recommends s.len() == p.len()
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if p[0] { s[0] } else { 0 }) + sumc(s.subrange(1, s.len() as int), p.subrange(1, p.len() as int))
    }
}

spec fn add_condition(lst: Seq<int>) -> Seq<bool> {
    Seq::new(lst.len(), |i: int| i % 2 == 1 && lst[i] % 2 == 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove sumc relationship for appending one element */
proof fn lemma_sumc_append(s: Seq<int>, p: Seq<bool>, x: int, px: bool)
    requires
        s.len() == p.len(),
    ensures
        sumc(s.push(x), p.push(px)) == sumc(s, p) + if px { x } else { 0 },
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(p.push(px) =~= seq![px]);
    } else {
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s.subrange(1, s.len() as int).push(x));
        assert(p.push(px).subrange(1, p.push(px).len() as int) =~= p.subrange(1, p.len() as int).push(px));
        lemma_sumc_append(s.subrange(1, s.len() as int), p.subrange(1, p.len() as int), x, px);
    }
}
// </vc-helpers>

// <vc-spec>
fn add(v: Vec<i8>) -> (r: i8)
    ensures r == sumc(v@.map_values(|x: i8| x as int), add_condition(v@.map_values(|x: i8| x as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed s computation to use spec function */
{
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    let ghost s = v@.map_values(|x: i8| x as int);
    let ghost p = add_condition(s);
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            s.len() == v.len(),
            p.len() == v.len(),
            sum as int == sumc(s.subrange(0, i as int), p.subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> s[j] == v[j] as int,
            forall|j: int| 0 <= j < i && p[j] ==> -64 <= sum as int + s[j] <= 63,
        decreases v.len() - i
    {
        let cond = i % 2 == 1 && v[i] % 2 == 0;
        assert(p[i as int] == cond);
        
        if cond {
            // Check for overflow before adding
            if v[i] > 0 && sum > 127 - v[i] {
                // Overflow would occur
                sum = 127; // Saturate at max
            } else if v[i] < 0 && sum < -128 - v[i] {
                // Underflow would occur
                sum = -128; // Saturate at min
            } else {
                sum = sum + v[i];
            }
        }
        
        proof {
            assert(s.subrange(0, (i + 1) as int) =~= s.subrange(0, i as int).push(s[i as int]));
            assert(p.subrange(0, (i + 1) as int) =~= p.subrange(0, i as int).push(p[i as int]));
            lemma_sumc_append(s.subrange(0, i as int), p.subrange(0, i as int), s[i as int], p[i as int]);
        }
        
        i = i + 1;
    }
    
    assert(s.subrange(0, v.len() as int) =~= s);
    assert(p.subrange(0, v.len() as int) =~= p);
    sum
}
// </vc-code>


}

fn main() {}