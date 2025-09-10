function pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

function repunit(n: nat): nat
    requires n >= 0
    ensures n == 0 ==> repunit(n) == 0
    ensures n > 0 ==> repunit(n) > 0
{
    if n == 0 then 0 
    else if n == 1 then 1
    else if n == 2 then 11
    else if n == 3 then 111
    else if n == 4 then 1111
    else if n == 5 then 11111
    else n  // simplified for larger values
}

predicate ValidInput(n: nat)
{
    true
}

predicate ValidOutput(n: nat, result: nat)
{
    (n == 0 ==> result == 0) &&
    (n > 0 ==> result > 0)
}

// <vc-helpers>
function pow10(n: nat): nat
  ensures n == 0 ==> pow10(n) == 1
  ensures n > 0 ==> pow10(n) == 10 * pow10(n - 1)
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  if n == 0 then return 0;

  var result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == (pow10(i) - 1) / 9
  {
    result := result + pow10(i);
    i := i + 1;
  }
  return result;
}
// </vc-code>

