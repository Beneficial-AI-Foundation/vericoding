predicate ValidInput(n: int, s: string)
{
  1 <= n <= 200000 && |s| == n && 
  forall i :: 0 <= i < n ==> s[i] == 'D' || s[i] == 'R'
}

function CountD(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s) >= 0
  ensures CountD(s) <= |s|
  ensures CountD(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'D'
{
  if |s| == 0 then 0
  else (if s[0] == 'D' then 1 else 0) + CountD(s[1..])
}

function CountR(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountR(s) >= 0
  ensures CountR(s) <= |s|
  ensures CountR(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'R'
{
  if |s| == 0 then 0
  else (if s[0] == 'R' then 1 else 0) + CountR(s[1..])
}

function OptimalEliminationGameWinner(s: string): string
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures OptimalEliminationGameWinner(s) == "D" || OptimalEliminationGameWinner(s) == "R"
  ensures CountD(s) == 0 ==> OptimalEliminationGameWinner(s) == "R"
  ensures CountR(s) == 0 ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> OptimalEliminationGameWinner(s) == "R"
  ensures OptimalEliminationGameWinner(s) == "D" ==> CountD(s) > 0
  ensures OptimalEliminationGameWinner(s) == "R" ==> CountR(s) > 0
{
  if CountD(s) == 0 then "R"
  else if CountR(s) == 0 then "D"
  else if CountD(s) >= CountR(s) then "D"
  else "R"
}

// <vc-helpers>
function GetWinner(n: int, s: string): string
  requires ValidInput(n, s)
  ensures GetWinner(n,s) == "D" || GetWinner(n,s) == "R"
  ensures GetWinner(n,s) == "D" ==> CountD(s) > 0
  ensures GetWinner(n,s) == "R" ==> CountR(s) > 0
  ensures CountD(s) == 0 ==> GetWinner(n,s) == "R"
  ensures CountR(s) == 0 ==> GetWinner(n,s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> GetWinner(n,s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> GetWinner(n,s) == "R"
  ensures GetWinner(n,s) == OptimalEliminationGameWinner(s)
{
    var q_d: seq<int> := [];
    var q_r: seq<int> := [];

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < |q_d| ==> 0 <= q_d[k] < n
        invariant forall k :: 0 <= k < |q_r| ==> 0 <= q_r[k] < n
        invariant forall k :: 0 <= k < |q_d| ==> s[q_d[k]] == 'D'
        invariant forall k :: 0 <= k < |q_r| ==> s[q_r[k]] == 'R'
    {
        if s[i] == 'D' {
            q_d := q_d + [i];
        } else {
            q_r := q_r + [i];
        }
    }

    while |q_d| > 0 && |q_r| > 0
        invariant forall k :: 0 <= k < |q_d| ==> 0 <= q_d[k] < n + n // The indices can exceed n due to addition of n
        invariant forall k :: 0 <= k < |q_r| ==> 0 <= q_r[k] < n + n // The indices can exceed n due to addition of n
        invariant forall k :: 0 <= k < |q_d| ==> s[q_d[k] % n] == 'D' // Check the original character using modulo
        invariant forall k :: 0 <= k < |q_r| ==> s[q_r[k] % n] == 'R' // Check the original character using modulo
        decreases |q_d| + |q_r|
    {
        var pd := q_d[0];
        var pr := q_r[0];
        q_d := q_d[1..];
        q_r := q_r[1..];

        if pd < pr {
            q_d := q_d + [pd + n];
        } else {
            q_r := q_r + [pr + n];
        }
    }

    if |q_d| > 0 then "D" else "R"
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
  requires ValidInput(n, s)
  ensures result == "D" || result == "R"
  ensures result == "D" ==> CountD(s) > 0
  ensures result == "R" ==> CountR(s) > 0
  ensures CountD(s) == 0 ==> result == "R"
  ensures CountR(s) == 0 ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> result == "R"
  ensures result == OptimalEliminationGameWinner(s)
// </vc-spec>
// <vc-code>
{
  return GetWinner(n, s);
}
// </vc-code>

