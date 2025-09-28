// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function HasTwoZeros(s: seq<int>, start: int, end: int): bool 
  requires 0 <= start <= end <= |s|
{
  if start + 1 >= end then false
  else exists i, j :: start <= i < j < end && s[i] == 0 && s[j] == 0
}

function HasTwoOnes(s: seq<int>, start: int, end: int): bool 
  requires 0 <= start <= end <= |s|
{
  if start + 1 >= end then false
  else exists i, j :: start <= i < j < end && s[i] == 1 && s[j] == 1
}

lemma ZeroZeroOneOneLemma(s: seq<int>, x: int, y: int, z: int, w: int)
  requires 0 <= x < y < z < w < |s|
  requires s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
  ensures exists x2, y2, z2, w2 :: 0 <= x2 < y2 < z2 < w2 < |s| && s[x2] == 0 && s[y2] == 0 && s[z2] == 1 && s[w2] == 1
{
}

/* helper modified by LLM (iteration 4): Added helper function to check if pattern exists in sequence */
function PatternExists(s: seq<int>): bool {
  exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 

    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Simplified implementation using helper function */
  res := PatternExists(s);
}
// </vc-code>
