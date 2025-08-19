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


// SPEC

// Quero agora implementar como uma função não recursiva
method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
}