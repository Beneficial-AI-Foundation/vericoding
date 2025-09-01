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

// <vc-helpers>
lemma iterate_to_odd_decreases(n: nat)
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) <= n / 2
{
  if (n / 2) % 2 == 1 {
    // n/2 is odd, so iterate_to_odd(n) = n/2 ≤ n/2
  } else {
    // Recursive case: iterate_to_odd(n) = iterate_to_odd(n/2)
    // By induction, iterate_to_odd(n/2) ≤ (n/2)/2 = n/4 ≤ n/2
    iterate_to_odd_decreases(n / 2);
  }
}

lemma iterate_to_odd_positive(n: nat)
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) > 0
{
  if (n / 2) % 2 == 1 {
    // n/2 is odd and positive since n > 0
  } else {
    // n/2 is even and positive, so recursive call
    iterate_to_odd_positive(n / 2);
  }
}

lemma iterate_to_odd_correct(n: nat)
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) == if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
{
  // This lemma is just the function definition, so no body needed
}

lemma iterate_to_odd_equals_loop(n: nat)
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) == get_temp_result(n)
{
  if (n / 2) % 2 == 1 {
    // Base case
  } else {
    iterate_to_odd_equals_loop(n / 2);
  }
}

function get_temp_result(n: nat): nat
  requires n % 2 == 0 && n > 0
{
  if (n / 2) % 2 == 1 then n / 2 else get_temp_result(n / 2)
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n % 2 == 0 {
    var temp := n;
    while temp % 2 == 0
      invariant temp > 0
      invariant temp % 2 == 0
      invariant iterate_to_odd(n) == iterate_to_odd(temp)
      decreases temp
    {
      temp := temp / 2;
      if temp % 2 != 0 {
        break;
      }
    }
    next := temp;
    assert next == iterate_to_odd(n);
  } else {
    var nn := 3 * n + 1;
    var temp := nn;
    while temp % 2 == 0
      invariant temp > 0
      invariant temp % 2 == 0
      invariant iterate_to_odd(nn) == iterate_to_odd(temp)
      decreases temp
    {
      temp := temp / 2;
      if temp % 2 != 0 {
        break;
      }
    }
    next := temp;
    assert next == iterate_to_odd(nn);
  }
}
// </vc-code>

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  assume{:axiom} false;
}
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  assume{:axiom} false;
}