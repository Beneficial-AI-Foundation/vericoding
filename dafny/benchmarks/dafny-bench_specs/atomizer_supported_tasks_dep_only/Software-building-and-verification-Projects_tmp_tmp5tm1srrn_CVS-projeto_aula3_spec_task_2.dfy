//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

// 2.
//ATOM_PLACEHOLDER_List// ATOM 

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}


// SPEC 

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{
}


// 3.
//ATOM_PLACEHOLDER_maxArray

// 5.
//ATOM_PLACEHOLDER_maxArrayReverse

// 6
//ATOM_PLACEHOLDER_sum

//ATOM_PLACEHOLDER_sumBackwards

