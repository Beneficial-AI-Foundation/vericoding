//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Triple1

//ATOM_PLACEHOLDER_DoubleQuadruple

// ATOM 

function F(): int {
29
}

//IMPL SPEC

method M() returns (r: int) 
ensures r == 29
{
    r := F();
}

//IMPL SPEC

method Caller() {
    // Empty method body - no preconditions or postconditions to satisfy
}

//IMPL SPEC

method M2() returns (r: int) 
ensures r == 29
{
    r := F();
}