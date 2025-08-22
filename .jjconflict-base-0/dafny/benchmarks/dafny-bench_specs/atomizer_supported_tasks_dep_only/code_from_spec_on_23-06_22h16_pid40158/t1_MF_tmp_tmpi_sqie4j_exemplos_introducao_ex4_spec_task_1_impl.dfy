// ATOM 
function Fat(n: nat): nat
{
   if n == 0 then 1 else n * Fat(n-1)
}

//IMPL 
method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
    if n == 0 {
        r := 1;
    } else {
        var temp := Fatorial(n-1);
        r := n * temp;
    }
}