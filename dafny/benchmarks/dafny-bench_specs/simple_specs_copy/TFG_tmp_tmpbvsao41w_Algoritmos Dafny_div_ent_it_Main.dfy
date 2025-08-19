//ATOM
method div_ent_it(a: int, b: int) returns (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

  requires a >= 0 && b > 0
  ensures a == b*c + r && 0 <= r < b
{
  c := 0;
  r := 0;
  assume a ==> b*c + r && 0 <= r < b;
  return c, r;
}


// SPEC

method Main()
{
  var c, r := div_ent_it(6 , 2) ;
  print "Cociente: ", c, ", Resto: ", r ;
}
