// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 2): fixed invalid 'function method' syntax */
function Insert(x: int, s: seq<int>): seq<int>
  requires IsSorted(s)
  ensures IsSorted(Insert(x, s))
  ensures multiset(Insert(x, s)) == multiset(s) + multiset{x}
  ensures |Insert(x, s)| == |s| + 1
  decreases |s|
{
  if s == [] then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

/* helper modified by LLM (iteration 2): fixed invalid 'function method' syntax */
function Sort(s: seq<int>): seq<int>
  ensures IsSorted(Sort(s))
  ensures multiset(Sort(s)) == multiset(s)
  ensures |Sort(s)| == |s|
  decreases |s|
{
  if s == [] then []
  else Insert(s[|s|-1], Sort(s[..|s|-1]))
}
// </vc-helpers>

// <vc-spec>
method maximum(s: seq<int>, k: int) returns (result: seq<int>)

  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000

  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented logic using sorting helpers */
  var sorted_s := Sort(s);
  result := sorted_s[|s|-k..];
}
// </vc-code>
