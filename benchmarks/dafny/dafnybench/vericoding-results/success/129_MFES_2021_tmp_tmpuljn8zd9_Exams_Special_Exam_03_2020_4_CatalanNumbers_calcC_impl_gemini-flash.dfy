function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

// <vc-helpers>
function C_iter(n: nat): nat
  decreases n
{
  if n == 0 then 1
  else (4 * n - 2) * C_iter(n - 1) / (n + 1)
}
  
lemma C_eq_C_iter(n: nat)
  ensures C(n) == C_iter(n)
{
  if n == 0 {
  } else {
    C_eq_C_iter(n-1);
  }
}
// </vc-helpers>

// <vc-spec>
method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
// </vc-spec>
// <vc-code>
{
  C_eq_C_iter(n);
  var current_C: nat := 1;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant current_C == C_iter(i)
    decreases n - i
  {
    current_C := (4 * i + 2) * current_C / (i + 2);
    i := i + 1;
  }
  res := current_C;
}
// </vc-code>

