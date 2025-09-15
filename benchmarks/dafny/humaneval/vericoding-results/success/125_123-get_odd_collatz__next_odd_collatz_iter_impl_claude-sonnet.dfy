// <vc-preamble>
function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}
function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added proper arithmetic proof for division properties */
lemma division_preserves_evenness(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures n / 2 > 0
{
  // When n is even and positive, n/2 is positive
}

lemma collatz_step_valid(n: nat)
  requires n > 0
  requires n % 2 == 1
  ensures 3 * n + 1 > 0
  ensures (3 * n + 1) % 2 == 0
{
  // 3 * odd + 1 is always even and positive
}
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)

  requires n > 0

  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Added explicit validation for iterate_to_odd preconditions */
  if n % 2 == 0 {
    next := iterate_to_odd(n);
  } else {
    var temp := 3 * n + 1;
    assert temp % 2 == 0;  // 3 * odd + 1 is even
    assert temp > 0;       // temp is positive
    collatz_step_valid(n);
    next := iterate_to_odd(temp);
  }
}
// </vc-code>
