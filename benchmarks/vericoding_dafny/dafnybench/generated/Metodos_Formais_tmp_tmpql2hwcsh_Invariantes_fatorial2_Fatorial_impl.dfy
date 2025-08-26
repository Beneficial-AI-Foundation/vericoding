function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
// </vc-spec>

// <vc-helpers>
// </vc-helpers>

// <vc-code>
{
  f := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant f == Fat(i)
    decreases n - i
  {
    i := i + 1;
    f := f * i;
  }
}
// </vc-code>

// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1