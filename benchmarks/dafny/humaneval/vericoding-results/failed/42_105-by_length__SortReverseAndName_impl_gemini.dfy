// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
predicate IsSortedDescending(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

function {:decreases |s|} Insert(x: int, s: seq<int>): seq<int>
  requires IsSortedDescending(s)
  ensures multiset(Insert(x, s)) == multiset(s) + multiset({x})
  ensures IsSortedDescending(Insert(x, s))
{
  if |s| == 0 then [x]
  else if x >= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

function {:decreases |s|} Sort(s: seq<int>): seq<int>
  ensures multiset(Sort(s)) == multiset(s)
  ensures IsSortedDescending(Sort(s))
{
  if |s| == 0 then []
  else Insert(s[0], Sort(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)

  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [Fixed compilation errors by using a while loop for filtering and a sequence constructor for mapping.] */
  var filtered: seq<int> := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |filtered| <= i
    invariant forall x :: x in filtered ==> 1 <= x <= 9
    decreases |arr| - i
  {
    if 1 <= arr[i] <= 9 {
      filtered := filtered + [arr[i]];
    }
    i := i + 1;
  }

  var sorted := Sort(filtered);
  
  assert forall x :: x in sorted ==> 1 <= x <= 9;

  result := seq(|sorted|, i => NumberToName(sorted[i]));
}
// </vc-code>
