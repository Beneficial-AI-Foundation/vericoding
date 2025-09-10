predicate ValidInput(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>)
{
    |attacking_powers| == s && |bases| == b
}

function SumGoldForSpaceship(attacking_power: nat, bases: seq<(nat, nat)>): nat
{
    if |bases| == 0 then 0
    else if attacking_power >= bases[0].0 then bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..])
    else SumGoldForSpaceship(attacking_power, bases[1..])
}

predicate ValidOutput(s: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>, result: seq<nat>)
{
    |result| == s &&
    (forall i :: 0 <= i < s ==> result[i] >= 0) &&
    (forall i :: 0 <= i < s && i < |attacking_powers| ==> result[i] == SumGoldForSpaceship(attacking_powers[i], bases))
}

// <vc-helpers>
function method SumGoldForSpaceship_memo(attacking_power: nat, bases: seq<(nat, nat)>, i: nat): nat
  requires i <= |bases|
{
  if i == |bases| then 0
  else if attacking_power >= bases[i].0 then bases[i].1 + SumGoldForSpaceship_memo(attacking_power, bases, i + 1)
  else SumGoldForSpaceship_memo(attacking_power, bases, i + 1)
}

lemma SumGoldForSpaceship_is_SumGoldForSpaceship_memo(attacking_power: nat, bases: seq<(nat, nat)>)
  ensures SumGoldForSpaceship(attacking_power, bases) == SumGoldForSpaceship_memo(attacking_power, bases, 0)
{
  if |bases| == 0 {
    assert SumGoldForSpaceship(attacking_power, bases) == 0;
    assert SumGoldForSpaceship_memo(attacking_power, bases, 0) == 0;
  } else {
    calc {
      SumGoldForSpaceship(attacking_power, bases);
      if attacking_power >= bases[0].0 then bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..])
      else SumGoldForSpaceship(attacking_power, bases[1..]);
      {
        SumGoldForSpaceship_is_SumGoldForSpaceship_memo(attacking_power, bases[1..]);
      }
      if attacking_power >= bases[0].0 then bases[0].1 + SumGoldForSpaceship_memo(attacking_power, bases[1..], 0)
      else SumGoldForSpaceship_memo(attacking_power, bases[1..], 0);
      SumGoldForSpaceship_memo(attacking_power, bases, 0);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>) returns (result: seq<nat>)
    requires ValidInput(s, b, attacking_powers, bases)
    ensures ValidOutput(s, attacking_powers, bases, result)
// </vc-spec>
// <vc-code>
{
    var res: seq<nat> := new nat[s];
    for i := 0 to s - 1
        invariant 0 <= i <= s
        invariant |res| == s
        invariant forall k :: 0 <= k < i ==> res[k] >= 0
        invariant forall k :: 0 <= k < i ==> res[k] == SumGoldForSpaceship(attacking_powers[k], bases)
    {
        // Proof that SumGoldForSpaceship is equivalent to SumGoldForSpaceship_memo
        SumGoldForSpaceship_is_SumGoldForSpaceship_memo(attacking_powers[i], bases);

        res[i] := SumGoldForSpaceship_memo(attacking_powers[i], bases, 0);
    }
    return res;
}
// </vc-code>

