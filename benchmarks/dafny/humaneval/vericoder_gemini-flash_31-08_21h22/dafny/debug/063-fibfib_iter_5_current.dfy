function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 then result := 0
  else if n == 2 then result := 1
  else
    var a_val : nat := 0; // fibfib(i-3)
    var b_val : nat := 0; // fibfib(i-2)
    var c_val : nat := 1; // fibfib(i-1)

    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant a_val == fibfib(i-3)
      invariant b_val == fibfib(i-2)
      invariant c_val == fibfib(i-1)
      decreases n - i
    {
      var next_c_val := a_val + b_val + c_val;
      a_val := b_val;
      b_val := c_val;
      c_val := next_c_val;
      i := i + 1;
    }
    result := c_val;
}
// </vc-code>

