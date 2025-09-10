predicate ValidInput(input: seq<string>)
{
    |input| == 8 &&
    (forall i :: 0 <= i < 8 ==> |input[i]| == 8) &&
    (forall i, j :: 0 <= i < 8 && 0 <= j < 8 ==> input[i][j] in {'W', 'B'})
}

predicate HasAlternatingRow(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
{
    forall k :: 1 <= k < 8 ==> row[k] != row[k-1]
}

predicate AllRowsHaveAlternatingPattern(input: seq<string>)
    requires ValidInput(input)
{
    forall i :: 0 <= i < 8 ==> HasAlternatingRow(input[i])
}

// <vc-helpers>
// No additional helpers required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
  var all := true;
  var i := 0;
  while i < 8
    invariant 0 <= i <= 8
    invariant all ==> (forall ii :: 0 <= ii < i ==> HasAlternatingRow(input[ii]))
  {
    var row := input[i];
    var okRow := true;
    var j := 1;
    while j < 8
      invariant 1 <= j <= 8
      invariant okRow ==> (forall k :: 1 <= k < j ==> row[k] != row[k-1])
    {
      if row[j] == row[j-1] {
        okRow := false;
        j := 8;
      } else {
        j := j + 1;
      }
    }
    if okRow {
      // From the inner loop invariants we know j == 8 and all adjacent pairs differ.
      assert j == 8;
      assert forall k :: 1 <= k < 8 ==> row[k] != row[k-1];
      // Thus this row satisfies HasAlternatingRow
      assert HasAlternatingRow(row);
    } else {
      all := false;
    }
    i := i + 1;
  }

  if all {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

