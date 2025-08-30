//ATOM
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
  if v==[] then 0
  else if |v|==1 then v[0]
  else v[0]+sum(v[1..])
}

//IMPL vector_Sum
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
  x := sum(v);
}