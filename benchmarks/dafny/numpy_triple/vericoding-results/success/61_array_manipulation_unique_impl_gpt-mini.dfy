// <vc-preamble>
// Method that finds unique elements in an array and returns them sorted
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert sequence to set */
function SeqToSet(s: seq<real>): set<real>
  decreases |s|
  ensures forall x :: x in SeqToSet(s) <==> x in s
{
  if |s| == 0 then {} else { s[0] } + SeqToSet(s[1..])
}

/* helper modified by LLM (iteration 4): index of minimal element in non-empty sequence */
function MinIndex(s: seq<real>): nat
  requires |s| > 0
  decreases |s|
  ensures 0 <= MinIndex(s) < |s|
  ensures forall j :: 0 <= j < |s| ==> s[MinIndex(s)] <= s[j]
{
  if |s| == 1 then 0 else
    var k := MinIndex(s[1..]) + 1;
    if s[0] <= s[k] then 0 else k
}

/* helper modified by LLM (iteration 4): find minimal element of non-empty sequence using MinIndex */
function MinSeq(s: seq<real>): real
  requires |s| > 0
  decreases |s|
  ensures exists i :: 0 <= i < |s| && MinSeq(s) == s[i]
  ensures forall x :: x in s ==> MinSeq(s) <= x
{
  s[MinIndex(s)]
}

/* helper modified by LLM (iteration 4): remove all occurrences of a value from sequence */
function RemoveAll(s: seq<real>, v: real): seq<real>
  decreases |s|
  ensures forall x :: x in RemoveAll(s, v) ==> x in s && x != v
  ensures forall x :: x in s && x != v ==> x in RemoveAll(s, v)
  ensures SeqToSet(RemoveAll(s, v)) == SeqToSet(s) - {v}
  ensures |RemoveAll(s, v)| <= |s|
  ensures v in s ==> |RemoveAll(s, v)| < |s|
{
  if |s| == 0 then [] else
    if s[0] == v then RemoveAll(s[1..], v) else [s[0]] + RemoveAll(s[1..], v)
}

// </vc-helpers>

// <vc-spec>
method numpy_unique(arr: seq<real>) returns (unique_arr: seq<real>)
  ensures // The result is sorted in ascending order
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] < unique_arr[j]
  ensures // No duplicates exist in the result
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] != unique_arr[j]
  ensures // Every element in result comes from the input array
          forall i :: 0 <= i < |unique_arr| ==> unique_arr[i] in arr
  ensures // Every distinct element from input appears in result
          forall x :: x in arr ==> x in unique_arr
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build sorted unique sequence by repeatedly taking minimum and removing duplicates */
  var remaining := arr;
  var seqRes: seq<real> := [];
  var seen: set<real> := {};
  while |remaining| > 0
    decreases |remaining|
    invariant 0 <= |remaining| <= |arr|
    invariant SeqToSet(seqRes) == seen
    invariant forall i, j :: 0 <= i < j < |seqRes| ==> seqRes[i] < seqRes[j]
    invariant forall i :: 0 <= i < |seqRes| ==> seqRes[i] in arr
    invariant SeqToSet(remaining) + seen == SeqToSet(arr)
    invariant forall x, y :: x in SeqToSet(seqRes) && y in remaining ==> x < y
  {
    var m := MinSeq(remaining);
    assert exists i :: 0 <= i < |remaining| && m == remaining[i];
    if !(m in seen) {
      seqRes := seqRes + [m];
      seen := seen + {m};
    }
    remaining := RemoveAll(remaining, m);
  }
  unique_arr := seqRes;
}

// </vc-code>
