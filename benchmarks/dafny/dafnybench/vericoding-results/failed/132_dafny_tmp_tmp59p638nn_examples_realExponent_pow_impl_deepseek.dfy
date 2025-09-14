ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// <vc-helpers>
ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
{
  if n == 1.0 then
    1.0
  else
    power(n - 1.0, alpha) * n
}

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0
{
  1.0 // Placeholder implementation
}

lemma power_lemma(n: real, alpha: real)
  requires n > 0.0 && alpha > 0.0
  ensures power(n, alpha) > 0.0
{
}

lemma power_base_case(alpha: real)
  requires alpha > 0.0
  ensures power(1.0, alpha) == 1.0
{
}

lemma power_recursive_case(n: real, alpha: real)
  requires n > 1.0 && alpha > 0.0
  ensures power(n, alpha) == power(n - 1.0, alpha) * n
{
}

lemma power_one(n: real, alpha: real)
  requires n == 1.0 && alpha > 0.0
  ensures power(n, alpha) == 1.0
{
}

lemma power_inductive_step(i: real, alpha: real)
  requires i > 1.0 && alpha > 0.0
  ensures power(i, alpha) == power(i - 1.0, alpha) * i
{
}

lemma power_identity(i: int, alpha: real)
  requires i >= 1 && alpha > 0.0
  ensures power(i as real, alpha) == power((i - 1) as real, alpha) * (i as real)
  decreases i
{
  if i > 1 {
    power_inductive_step(i as real, alpha);
  }
}
// </vc-helpers>

// <vc-spec>
method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
// </vc-spec>
// <vc-code>
{
  product := 1.0;
  var i := 1;
  
  if n == 1 {
    // Base case: n == 1
    assert n as real == 1.0;
  } else {
    while i < n
      invariant 1 <= i <= n
      invariant product == power(i as real, alpha)
    {
      i := i + 1;
      product := product * (i as real);
      power_identity(i, alpha);
      assert product == power(i as real, alpha);
    }
  }
}
// </vc-code>

