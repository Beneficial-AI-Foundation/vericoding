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
    var f1 := 0; // fibfib(i-3) -> fibfib(0) always true
    var f2 := 1; // fibfib(i-2) -> fibfib(1) when i = 3; fibfib(1) is 0, so f2 needs to be 0
    var f3 := 0; // fibfib(i-1) -> fibfib(2) when i = 3; fibfib(2) is 1, so f3 needs to be 1

    // Initial values for i = 3:
    // fibfib(0) = 0
    // fibfib(1) = 0
    // fibfib(2) = 1

    f1 := 0; // fibfib(i-3) for i=3 is fibfib(0) = 0
    f2 := 0; // fibfib(i-2) for i=3 is fibfib(1) = 0
    f3 := 1; // fibfib(i-1) for i=3 is fibfib(2) = 1

    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant f3 == fibfib(i-1)
      invariant f2 == fibfib(i-2)
      invariant f1 == fibfib(i-3)
    {
      var next_f := f3 + f2 + f1;
      f1 := f2;
      f2 := f3;
      f3 := next_f;
      i := i + 1;
    }
    result := f3;
}
// </vc-code>

