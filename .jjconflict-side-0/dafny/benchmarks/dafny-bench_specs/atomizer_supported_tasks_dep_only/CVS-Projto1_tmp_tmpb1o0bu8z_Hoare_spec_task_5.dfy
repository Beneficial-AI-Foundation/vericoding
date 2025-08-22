//ATOM_PLACEHOLDER_Max

//ATOM_PLACEHOLDER_Test

//ATOM_PLACEHOLDER_m1



//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib


//ATOM_PLACEHOLDER_List// ATOM 

function add(l:List<int>) : int
{
    match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}



// SPEC 


method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
{
}



//ATOM_PLACEHOLDER_MaxA



