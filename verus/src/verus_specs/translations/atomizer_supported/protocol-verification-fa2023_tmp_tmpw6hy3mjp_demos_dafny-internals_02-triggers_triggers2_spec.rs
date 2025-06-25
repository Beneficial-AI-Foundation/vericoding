// ATOM 
spec fn f(x: int) -> int;
// ATOM 

spec fn ff(x: int) -> int;

proof fn ff_eq()
    ensures forall|x: int| #[trigger] ff(x) == f(f(x)),
{
}

proof fn ff_eq2()
    ensures forall|x: int| #[trigger] f(f(x)) == ff(x),
{
}

proof fn ff_eq_bad()
    ensures forall|x: int| ff(x) == f(f(x)),
{
}

// ATOM 

proof fn use_ff(x: int)
{
}

// ATOM 

proof fn use_ff2(x: int)
{
}