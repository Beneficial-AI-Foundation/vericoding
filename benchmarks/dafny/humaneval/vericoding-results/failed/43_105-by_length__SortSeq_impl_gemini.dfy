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
predicate Sorted(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

/* helper modified by LLM (iteration 2): named return value in Insert function to fix compilation error */
function Insert(x: int, s: seq<int>): (res: seq<int>)
  requires Sorted(s)
  ensures Sorted(res)
  ensures |res| == |s| + 1
  ensures multiset(res) == multiset(s) + multiset({x})
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): retaining correct insertion sort implementation */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant Sorted(sorted)
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := Insert(s[i], sorted);
    i := i + 1;
  }
}
// </vc-code>
