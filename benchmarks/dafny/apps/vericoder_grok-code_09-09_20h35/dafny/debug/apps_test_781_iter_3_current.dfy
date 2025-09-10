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

// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
  var allAlt: bool := true;
  var i := 0;
  while i < 8
    invariant 0 <= i <= 8
    invariant allAlt == (forall k :: 0 <= k < i ==> HasAlternatingRow(input[k]))
  {
    allAlt := allAlt && HasAlternatingRow(input[i]);
    i := i + 1;
  }
  if allAlt {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

