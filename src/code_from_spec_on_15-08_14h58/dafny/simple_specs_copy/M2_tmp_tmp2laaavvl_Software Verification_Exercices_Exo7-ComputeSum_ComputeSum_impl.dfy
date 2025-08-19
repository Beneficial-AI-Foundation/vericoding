//ATOM
function Sum(n:nat):nat
 
{
 if n==0 then 0 else n + Sum(n-1)
}


//IMPL
method ComputeSum(n:nat) returns (s:nat)
  ensures s ==Sum(n)
{
  /* code modified by LLM (iteration 1): removed invalid text at beginning of file and fixed loop invariant */
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == Sum(i)
  {
    i := i + 1;
    s := s + i;
  }
}