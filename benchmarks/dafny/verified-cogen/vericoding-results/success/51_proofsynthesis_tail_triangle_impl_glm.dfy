// <vc-preamble>
function triangle(n: nat): nat
    decreases n
{
    if n == 0 then
        0
    else
        n + triangle(n - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method tail_triangle(n: nat, idx: nat, sum: nat) returns (new_sum: nat)
    requires idx <= n
    requires sum == triangle(idx)
    requires triangle(n) < 0x1_0000_0000
    ensures new_sum == triangle(n)
// </vc-spec>
// <vc-code>
{
  var i := idx;
  var current_sum := sum;
  
  while i < n
    invariant i <= n
    invariant current_sum == triangle(i)
  {
    current_sum := current_sum + (i + 1);
    i := i + 1;
  }
  
  new_sum := current_sum;
}
// </vc-code>
