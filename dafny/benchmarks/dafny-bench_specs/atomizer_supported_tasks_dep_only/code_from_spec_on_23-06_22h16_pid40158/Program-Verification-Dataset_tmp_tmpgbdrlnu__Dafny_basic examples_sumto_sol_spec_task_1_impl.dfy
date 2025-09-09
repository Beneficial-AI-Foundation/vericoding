// ATOM 
function sum_up_to (n: nat): nat
{
  if (n == 0) then 0
  else sum_up_to (n-1) + 1
}

//IMPL 
method SumUpTo (n: nat) returns (r: nat)
  ensures r == sum_up_to (n);
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == sum_up_to(i)
  {
    r := r + 1;
    i := i + 1;
  }
}

//ATOM_PLACEHOLDER_total

//ATOM_PLACEHOLDER_total_lemma

//ATOM_PLACEHOLDER_Total