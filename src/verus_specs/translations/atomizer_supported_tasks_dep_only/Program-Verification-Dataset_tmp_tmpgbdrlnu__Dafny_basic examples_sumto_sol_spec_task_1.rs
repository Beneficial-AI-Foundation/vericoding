// ATOM 
pub open spec fn sum_up_to(n: nat) -> nat {
    if n == 0 { 0 } else { sum_up_to((n-1) as nat) + 1 }
}

// SPEC 
pub fn SumUpTo(n: nat) -> (r: nat)
    ensures r == sum_up_to(n)
{
}

//ATOM_PLACEHOLDER_total

//ATOM_PLACEHOLDER_total_lemma

//ATOM_PLACEHOLDER_Total