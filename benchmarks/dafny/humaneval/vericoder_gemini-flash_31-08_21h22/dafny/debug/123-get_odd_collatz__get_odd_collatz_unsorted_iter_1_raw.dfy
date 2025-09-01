```vc-helpers
function iterate_to_odd_helper(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd_helper(n) else iterate_to_odd_helper(3 * n + 1)
}

method next_odd_collatz_iter_helper(n: nat) returns (next: nat)
  requires n > 0
  ensures next % 2 == 1
  ensures next == next_odd_collatz_helper(n)
{
  if n % 2 == 0 {
    var current_n := n;
    while current_n % 2 == 0
      ensures current_n % 2 == 0 || current_n % 2 == 1
      decreases current_n
    {
      if (current_n / 2) % 2 == 1 {
        current_n := current_n / 2;
        break;
      } else {
        current_n := current_n / 2;
      }
    }
    next := current_n;
    assert next == iterate_to_odd_helper(n); // Proof of correctness
  } else {
    var m := 3 * n + 1;
    assert m % 2 == 0; // Since n is odd, 3*n is odd, 3*n+1 is even.
    var current_m := m;
    while current_m % 2 == 0
      ensures current_m % 2 == 0 || current_m % 2 == 1
      decreases current_m
    {
      if (current_m / 2) % 2 == 1 {
        current_m := current_m / 2;
        break;
      } else {
        current_m := current_m / 2;
      }
    }
    next := current_m;
    assert next == iterate_to_odd_helper(3 * n + 1); // Proof of correctness
  }
}
```

```vc-code
{
  if n == 1 {
    return []; // As per problem constraints, this should not be reached due to n > 1
  }

  var current := n;
  var odd_collatz_list: seq<nat> := [];

  while current != 1
    ensures forall i :: 0 <= i < |odd_collatz_list| ==> odd_collatz_list[i] % 2 == 1
    decreases current
  {
    var next_val: nat;
    next_odd_collatz_iter_helper(current); // Call the helper method that calculates and asserts correctness
    next_val := next_odd_collatz_helper(current); // Use the function to get next_val

    if current % 2 == 1 {
      odd_collatz_list := odd_collatz_list + [current];
    }
    current := next_val;
  }
  odd_collatz_list := odd_collatz_list + [current]; // Add the final 1

  return odd_collatz_list;
}
```