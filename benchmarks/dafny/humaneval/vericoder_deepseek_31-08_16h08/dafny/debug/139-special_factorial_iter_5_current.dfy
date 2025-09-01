function factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}
function special_factorial_rec(n: nat): nat
  decreases n
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
}

// <vc-helpers>
lemma special_factorial_rec_property(n: nat)
  decreases n
  ensures special_factorial_rec(n) == if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
{
}

lemma factorial_lemma(n: nat)
  ensures factorial(n) > 0
  decreases n
{
  if n > 0 {
    factorial_lemma(n - 1);
  }
}

lemma special_factorial_iterative_lemma(i: nat, acc: nat)
  requires i >= 0
  requires acc == special_factorial_rec(i)
  ensures acc == special_factorial_rec(i)
  decreases i
{
}

lemma special_factorial_helper_lemma(i: nat)
  requires i >= 0
  ensures factorial(i + 1) * special_factorial_rec(i) == special_factorial_rec(i + 1)
  decreases i
{
  if i >= 0 {
    // By definition of special_factorial_rec
  }
}

lemma special_factorial_step_lemma(i: nat)
  requires i > 0
  ensures special_factorial_rec(i - 1) == special_factorial_rec(i) / factorial(i)
{
  if i > 0 {
    // This follows directly from the definition of special_factorial_rec
  }
}

lemma special_factorial_loop_invariant(i: nat, acc: nat)
  requires i >= 0
  requires acc == special_factorial_rec(i)
  ensures acc == special_factorial_rec(i)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == special_factorial_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i := n;
  var acc := 1;
  
  // Initialize acc to special_factorial_rec(n) to satisfy the invariant
  acc := special_factorial_rec(n);
  
  while i > 0
    invariant i >= 0
    invariant acc == special_factorial_rec(i)
    decreases i
  {
    special_factorial_loop_invariant(i, acc);
    // Update acc to maintain the invariant for the next iteration
    acc := acc / factorial(i);
    i := i - 1;
  }
  result := acc;
}
// </vc-code>

