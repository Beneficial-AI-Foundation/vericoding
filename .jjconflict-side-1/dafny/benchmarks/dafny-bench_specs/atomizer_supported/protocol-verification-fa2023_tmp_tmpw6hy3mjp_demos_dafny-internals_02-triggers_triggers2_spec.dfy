// ATOM 
function f(x: int): int
// ATOM 

function ff(x: int): int
 ff_eq()
  ensures forall x {:trigger ff(x)} :: ff(x) == f(f(x))

 ff_eq2()
  ensures forall x {:trigger f(f(x))} :: ff(x) == f(f(x))

 ff_eq_bad()
  // dafny ignores this trigger because it's an obvious loop
  ensures forall x {:trigger {f(x)}} :: ff(x) == f(f(x))

// ATOM 

lemma use_ff(x: int)
{
  ff_eq();
}


// ATOM 

lemma use_ff2(x: int)
{
  ff_eq2();
}




