predicate ValidInput(n: int, rows: seq<string>)
{
    n >= 0 && |rows| == n && forall i :: 0 <= i < |rows| ==> |rows[i]| == 5
}

predicate HasAdjacentEmptySeats(rows: seq<string>)
{
    exists i :: 0 <= i < |rows| && 
        ((|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
         (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

predicate NoAdjacentEmptySeats(rows: seq<string>)
{
    forall i :: 0 <= i < |rows| ==> 
        !((|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
          (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

predicate ValidSolution(result: string, rows: seq<string>)
{
    result != "NO" ==> |result| >= 4
}

// <vc-helpers>
// No helper declarations needed.
// </vc-helpers>

// <vc-spec>
method solve(n: int, rows: seq<string>) returns (result: string)
    requires ValidInput(n, rows)
    ensures result == "NO" || |result| >= 4
    ensures result == "NO" ==> NoAdjacentEmptySeats(rows)
    ensures result != "NO" ==> HasAdjacentEmptySeats(rows)
    ensures ValidSolution(result, rows)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var idx := -1;
  while i < |rows| && idx == -1
    invariant 0 <= i <= |rows|
    invariant idx == -1 ==> (forall k :: 0 <= k < i ==>
      !((|rows[k]| >= 2 && rows[k][0] == 'O' && rows[k][1] == 'O') ||
        (|rows[k]| >= 5 && rows[k][3] == 'O' && rows[k][4] == 'O')) )
    invariant idx != -1 ==> (0 <= idx < |rows| &&
      ((|rows[idx]| >= 2 && rows[idx][0] == 'O' && rows[idx][1] == 'O') ||
       (|rows[idx]| >= 5 && rows[idx][3] == 'O' && rows[idx][4] == 'O')))
    decreases |rows| - i
  {
    if ( (|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
         (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O') ) {
      idx := i;
    }
    i := i + 1;
  }

  if idx != -1 {
    // witness for HasAdjacentEmptySeats(rows)
    assert 0 <= idx < |rows|;
    assert (|rows[idx]| >= 2 && rows[idx][0] == 'O' && rows[idx][1] == 'O') ||
           (|rows[idx]| >= 5 && rows[idx][3] == 'O' && rows[idx][4] == 'O');
    assert (exists j :: 0 <= j < |rows| &&
      ((|rows[j]| >= 2 && rows[j][0] == 'O' && rows[j][1] == 'O') ||
       (|rows[j]| >= 5 && rows[j][3] == 'O' && rows[j][4] == 'O')));
    result := "YES\n";
  } else {
    // no such index -> NoAdjacentEmptySeats(rows)
    assert (forall k :: 0 <= k < |rows| ==>
      !((|rows[k]| >= 2 && rows[k][0] == 'O' && rows[k][1] == 'O') ||
        (|rows[k]| >= 5 && rows[k][3] == 'O' && rows[k][4] == 'O')) );
    result := "NO";
  }
}
// </vc-code>

