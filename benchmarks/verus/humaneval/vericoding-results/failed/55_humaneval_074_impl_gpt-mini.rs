// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn total_chars(lst: Seq<Seq<char>>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        lst[0].len() + total_chars(lst.subrange(1, lst.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec<Vec<char>> to Seq<Seq<char>> */
spec fn vecs_to_seqs(lst: Vec<Vec<char>>) -> Seq<Seq<char>>
{
    lst@.map_values(|v: Vec<char>| { v@ })
}

/* helper modified by LLM (iteration 5): prefix sum of character lengths for sequence of sequences */
spec fn prefix_chars(s: Seq<Seq<char>>, n: nat) -> nat
    requires n <= s.len(),
    decreases n
{
    if n == 0 { 0 } else { s@[n-1].len() + prefix_chars(s, n-1) }
}

/* helper modified by LLM (iteration 5): lemma for prefix_chars increment */
proof fn prefix_chars_cons(s: Seq<Seq<char>>, n: nat)
    requires n + 1 <= s.len()
    ensures prefix_chars(s, n + 1) == prefix_chars(s, n) + s@[n].len()
{
    proof {
        assert(prefix_chars(s, n + 1) == s@[n].len() + prefix_chars(s, n));
    }
}

// </vc-helpers>

// <vc-spec>
fn total_match(lst1: Vec<Vec<char>>, lst2: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures 
        result@ == lst1@ || result@ == lst2@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) <= total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst1@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) > total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst2@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variables updated via ghost blocks to track spec sums */
    let ghost s1: Seq<Seq<char>> = vecs_to_seqs(lst1);
    let ghost s2: Seq<Seq<char>> = vecs_to_seqs(lst2);

    let len1 = lst1.len();
    let len2 = lst2.len();

    let mut i: usize = 0;
    let mut rsum1: usize = 0;
    let ghost gi: nat = 0;
    let ghost sum1: nat = 0;
    while i < len1
        invariant
            i <= len1,
            gi == i as nat,
            sum1 == prefix_chars(s1, gi),
            rsum1 as nat == sum1,
        decreases len1 - i
    {
        let old_i = i;
        let v = &lst1[old_i];
        rsum1 = rsum1 + v.len();
        i = old_i + 1;
        proof {
            let old_gi = gi;
            let old_sum = sum1;
            assert(s1@[old_gi] == (*v)@);
            ghost { gi = old_gi + 1, sum1 = old_sum + s1@[old_gi].len(), }
            assert(rsum1 as nat == sum1);
        }
    }

    let mut j: usize = 0;
    let mut rsum2: usize = 0;
    let ghost gj: nat = 0;
    let ghost sum2: nat = 0;
    while j < len2
        invariant
            j <= len2,
            gj == j as nat,
            sum2 == prefix_chars(s2, gj),
            rsum2 as nat == sum2,
        decreases len2 - j
    {
        let old_j = j;
        let v = &lst2[old_j];
        rsum2 = rsum2 + v.len();
        j = old_j + 1;
        proof {
            let old_gj = gj;
            let old_sum = sum2;
            assert(s2@[old_gj] == (*v)@);
            ghost { gj = old_gj + 1, sum2 = old_sum + s2@[old_gj].len(), }
            assert(rsum2 as nat == sum2);
        }
    }

    if rsum1 <= rsum2 {
        lst1
    } else {
        lst2
    }
}

// </vc-code>


}

fn main() {}