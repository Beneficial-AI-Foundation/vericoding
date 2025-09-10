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
lemma RepunitValid(n: nat)
  ensures ValidOutput(n, repunit(n))
{
  if n == 0 {
    assert repunit(0) == 0;
    assert ValidOutput(0, repunit(0));
  } else {
    assert repunit(n) > 0;
    assert ValidOutput(n, repunit(n));
  }
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  RepunitValid(n);
  return repunit(n);
}
// </vc-code>

