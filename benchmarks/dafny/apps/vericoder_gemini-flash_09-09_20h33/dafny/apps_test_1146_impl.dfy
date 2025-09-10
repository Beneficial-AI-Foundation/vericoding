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
lemma CanTurnOnAllBulbsBody(m: nat, buttons: seq<seq<nat>>)
  ensures CanTurnOnAllBulbs(m, buttons) <==> (|unionOfAllBulbs(buttons)| == m)
{
  // This lemma is a direct consequence of the definition of CanTurnOnAllBulbs,
  // so no further proof steps are strictly necessary within the lemma body itself
  // for Dafny to verify it. It mainly serves to make the body of the `solve` method
  // cleaner if needed, but in this specific case, the definition is already simple enough.
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
    if CanTurnOnAllBulbs(m, buttons)
    {
        result := "YES";
    }
    else
    {
        result := "NO";
    }
    return result;
}
// </vc-code>

