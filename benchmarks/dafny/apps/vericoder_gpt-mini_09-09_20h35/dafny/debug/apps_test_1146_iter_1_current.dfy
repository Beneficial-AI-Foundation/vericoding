predicate ValidInput(n: nat, m: nat, buttons: seq<seq<nat>>)
{
    |buttons| == n &&
    n >= 1 && m >= 1 &&
    forall i :: 0 <= i < n ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
}

function unionOfAllBulbs(buttons: seq<seq<nat>>): set<nat>
{
    set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]
}

predicate CanTurnOnAllBulbs(m: nat, buttons: seq<seq<nat>>)
{
    |unionOfAllBulbs(buttons)| == m
}

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := set<int>{};
  while i < n
    invariant 0 <= i <= n
    invariant s == set x | exists p,q :: 0 <= p < i && 0 <= q < |buttons[p]| :: buttons[p][q]
    decreases n - i
  {
    var j := 0;
    var s_row := s;
    while j < |buttons[i]|
      invariant 0 <= j <= |buttons[i]|
      invariant s == set x | exists p,q :: (0 <= p < i && 0 <= q < |buttons[p]|) || (p == i && 0 <= q < j) :: buttons[p][q]
      decreases |buttons[i]| - j
    {
      s := s + { buttons[i][j] };
      j := j + 1;
    }
    // After processing row i, s includes all elements from rows 0..i
    i := i + 1;
  }

  assert s == unionOfAllBulbs(buttons);
  if |s| == m {
    result := "YES";
  } else {
    result := "NO";
  }

  // Relate result to specification
  assert (result == "YES") <==> (|s| == m);
  assert (|s| == m) <==> (|unionOfAllBulbs(buttons)| == m);
}
// </vc-code>

