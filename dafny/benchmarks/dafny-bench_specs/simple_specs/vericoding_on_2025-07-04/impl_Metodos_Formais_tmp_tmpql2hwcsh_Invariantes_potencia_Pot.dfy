//ATOM
// Potência

// deve ser especificado a potência, porque ele não existe n dafny

// Função recursiva da potência
function Potencia(x:nat, y:nat):nat
{
  if y == 0
  then 1
  else x * Potencia(x,y-1)
}

//IMPL 
method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
  r := 1;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == Potencia(x, i)
  {
    r := r * x;
    i := i + 1;
  }
}