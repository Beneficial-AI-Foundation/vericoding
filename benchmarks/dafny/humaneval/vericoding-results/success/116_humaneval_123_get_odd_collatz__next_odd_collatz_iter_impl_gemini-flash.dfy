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
/* helper modified by LLM (iteration 2): The previous helper, `IsOdd`, was unused and thus removed. No helpers are needed for this problem, so this section is left empty. */
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)

  requires n > 0

  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Logic adjusted to correctly handle both even and odd `n` and ensure the `next` value is the same as `next_odd_collatz(n)` */
{
    var current_val := n;

    if current_val % 2 == 0 {
        next := iterate_to_odd(current_val);
    } else {
        next := iterate_to_odd(3 * current_val + 1);
    }
}
// </vc-code>
