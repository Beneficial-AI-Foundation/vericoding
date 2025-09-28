// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  multiset(a) == multiset(b)
}

// Main method specification for msort
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): corrected function postconditions to reference function names and kept recursive definitions */
function Insert(x: real, s: seq<real>): seq<real>
  requires IsSorted(s)
  ensures IsSorted(Insert(x, s))
  ensures IsPermutation(s + [x], Insert(x, s))
  ensures |Insert(x, s)| == |s| + 1
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

/* helper modified by LLM (iteration 2): corrected function postconditions to reference function names */
function Sort(s: seq<real>): seq<real>
  ensures |Sort(s)| == |s|
  ensures IsSorted(Sort(s))
  ensures IsPermutation(s, Sort(s))
  decreases |s|
{
  if |s| <= 1 then s
  else Insert(s[0], Sort(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): delegate sorting to proven functional Sort */
  result := Sort(a);
}
// </vc-code>
