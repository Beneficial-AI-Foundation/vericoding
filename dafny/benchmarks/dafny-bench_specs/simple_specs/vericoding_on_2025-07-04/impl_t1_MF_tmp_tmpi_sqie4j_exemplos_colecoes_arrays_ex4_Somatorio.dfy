//ATOM
function SomaAte(a:array<nat>, i:nat):nat
 requires 0 <= i <= a.Length
 reads a
{
  if i == 0
  then 0
  else a[i-1] + SomaAte(a,i-1)
}

//IMPL 
method Somatorio(a:array<nat>) returns (s:nat)
 ensures s == SomaAte(a,a.Length)
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == SomaAte(a, i)
  {
    /* code modified by LLM (iteration 2): Added assertion to establish bounds and recursive relationship */
    assert i + 1 <= a.Length;
    assert SomaAte(a, i+1) == a[i] + SomaAte(a, i);
    
    s := s + a[i];
    i := i + 1;
    
    /* code modified by LLM (iteration 2): Added assertion to verify the invariant holds after updates */
    assert s == a[i-1] + SomaAte(a, i-1);
    assert s == SomaAte(a, i);
  }
}