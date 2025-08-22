//ATOM
/* code modified by LLM (iteration 1): added return statement to fix compilation error */
function f(x: int): int
{
  x
}

//ATOM
/* code modified by LLM (iteration 1): added return statement to fix compilation error */
function ff(x: int): int
{
  x
}

//ATOM
lemma ff_eq()
  ensures forall x {:trigger ff(x)} :: ff(x) == f(f(x))
{
}

//ATOM
lemma ff_eq2()
  ensures forall x {:trigger f(f(x))} :: ff(x) == f(f(x))
{
}

//ATOM
lemma ff_eq_bad()
  // dafny ignores this trigger because it's an obvious loop
  ensures forall x {:trigger f(x)} :: ff(x) == f(f(x))
{
}

//ATOM
lemma use_ff(x: int)
{
  ff_eq();
}

//ATOM
lemma use_ff2(x: int)
{
  ff_eq2();
}