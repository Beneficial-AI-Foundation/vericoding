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
    var a := 0; // fibfib(i-3)
    var b := 1; // fibfib(i-2) (when i=3, b=fibfib(1)=0, but also fibfib(0)=0 and fibfib(2)=1, so b=fibfib(i-2) is not i-2, but i-1 actually. This makes sense for the base case values where a=fibfib(0), b=fibfib(1), c=fibfib(2).
    // The previous implementation used a=0, b=0, c=1 for i=3, meaning fibfib(0), fibfib(1), fibfib(2) where fibfib(0)=0, fibfib(1)=0, fibfib(2)=1.
    // So if a=fibfib(i-3), b=fibfib(i-2), c=fibfib(i-1)
    // When i=3: a=fibfib(0)=0, b=fibfib(1)=0, c=fibfib(2)=1
    // The previous initial values where a=0, b=0, c=1 for i=3 are correct.
    // The issue is in the loop conditions. Let's trace it.
    var c_val : nat := 1; // fibfib(i-1)
    var b_val : nat := 0; // fibfib(i-2)
    var a_val : nat := 0; // fibfib(i-3)

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

