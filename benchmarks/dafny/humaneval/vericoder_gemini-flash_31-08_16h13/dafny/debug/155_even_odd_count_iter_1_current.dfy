

// <vc-helpers>
function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}

function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures even == even_count(n)
  ensures odd == odd_count(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var e_count := 0;
  var o_count := 0;
  var temp_n := n;

  while temp_n > 0
    invariant temp_n >= 0
    invariant e_count + o_count == (n - temp_n) / 10 + (n % 10 != 0 ? 1 : 0) // This invariant is tricky to get right
    invariant e_count == even_count(n / (temp_n * 10^(var_len(temp_n)))) if temp_n!=0
    invariant o_count == odd_count(n / (temp_n * 10^(var_len(temp_n)))) if temp_n!=0
    // A simpler invariant that the loop maintains the counts for the part of 'n' already processed.
    // The total counts 'even' and 'odd' after processing 'n' should match the mathematical functions.
    // Let's rely on the definition of even_count and odd_count functions and prove them correct.
    // For the loop, we are essentially building up the counts from right-to-left.
    // Let N_processed be the part of original n that has already been processed (i.e. removed from temp_n).
    // Let N_remaining be temp_n.
    // At each iteration, we process one digit (temp_n % 10).
    // We need to show that e_count is even_count(N_processed) and o_count is odd_count(N_processed).
    // This is hard since we add the digit directly.

    // Let's try invariants based on building up the count from processed digits
    invariant e_count + even_count(temp_n) == even_count(n)
    invariant o_count + odd_count(temp_n) == odd_count(n)
  {
    var digit := temp_n % 10;
    if digit % 2 == 0 {
      e_count := e_count + 1;
    } else {
      o_count := o_count + 1;
    }
    temp_n := temp_n / 10;
  }
  return e_count, o_count;
}
// </vc-code>

function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
// pure-end
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// pure-end