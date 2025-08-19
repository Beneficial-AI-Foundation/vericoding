//ATOM
function Fat(n:nat):nat
{
  if n == 0 then 1 else n*Fat(n-1)
}

//IMPL 
method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
  if n == 0 {
    f := 1;
  } else {
    var temp := Fatorial(n-1);
    f := n * temp;
  }
}