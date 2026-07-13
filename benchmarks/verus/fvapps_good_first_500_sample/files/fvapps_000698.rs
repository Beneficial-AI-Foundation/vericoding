// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn calculate_roses_spec(boys: nat, girls: nat) -> nat 
    recommends boys > 0 && girls > 0
{
    ((2 * ((boys + girls) - 1)) as nat)
}

fn calculate_roses(boys: nat, girls: nat) -> (result: nat)
    requires boys > 0 && girls > 0,
    ensures result % 2 == 0 && result >= 0 && result == calculate_roses_spec(boys, girls),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


proof fn roses_is_even(boys: nat, girls: nat)
    requires boys > 0 && girls > 0,
    ensures calculate_roses_spec(boys, girls) % 2 == 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn roses_is_nonnegative(boys: nat, girls: nat)
    requires boys > 0 && girls > 0,
    ensures calculate_roses_spec(boys, girls) >= 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn roses_formula(boys: nat, girls: nat)
    requires boys > 0 && girls > 0,
    ensures calculate_roses_spec(boys, girls) == ((2 * ((boys + girls) - 1)) as nat),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn equal_boys_girls(n: nat)
    requires n > 0,
    ensures calculate_roses_spec(n, n) == ((2 * (2 * n - 1)) as nat),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn minimum_case()
    ensures calculate_roses_spec(1, 1) == 2,
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // assert(calculate_roses(2, 3) == 8);
    // assert(calculate_roses(3, 3) == 10);
    // assert(calculate_roses(1, 1) == 2);
}