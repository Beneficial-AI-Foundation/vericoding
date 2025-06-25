//ATOM
function Potencia(x: nat, y: nat): nat
{
  if y == 0
  then 1
  else x * Potencia(x, y-1) 
}

//IMPL
method Pot(x: nat, y: nat) returns (r: nat)
ensures r == Potencia(x,y)
{
  /* code modified by LLM (iteration 2): Fixed initialization and loop structure */
  r := 1;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r * Potencia(x, y - i) == Potencia(x, y)
  {
    /* code modified by LLM (iteration 2): Added proper guards and lemma calls */
    assert i < y;
    assert y - i > 0;
    PotenciaLemma(x, y - i);
    assert Potencia(x, y - i) == x * Potencia(x, y - i - 1);
    r := r * x;
    i := i + 1;
    /* code modified by LLM (iteration 2): Added assertion to help maintain invariant */
    assert r * Potencia(x, y - i) == Potencia(x, y);
  }
}

/* code modified by LLM (iteration 2): Added helper lemma to prove Potencia property */
lemma PotenciaLemma(x: nat, y: nat)
  requires y > 0
  ensures Potencia(x, y) == x * Potencia(x, y - 1)
{
  // This follows directly from the definition of Potencia
}