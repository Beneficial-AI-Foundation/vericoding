//ATOM
function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
  if a < b then a else b
}

//IMPL
method minMethod(a: int, b: int) returns (c: int)
  ensures c <= a && c <= b
  ensures c == a || c == b
  // Ou encore:
  ensures c == min(a, b)
{
  c := min(a, b);
}