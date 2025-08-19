//ATOM

function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
  if a < b then a else b
}


// SPEC

method Main(){
  var integer:= min(1,2);
  print(integer);
}