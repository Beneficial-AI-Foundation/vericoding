// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Repeat function */
function Repeat(c: char, n: nat): seq<char>
{
  if n == 0 then [] else [c] + Repeat(c, n-1)
}

/* helper modified by LLM (iteration 5): DecodeRle append lemma */
lemma DecodeRle_Append(res: seq<(char, nat)>, c: char, cnt: nat)
  requires cnt > 0
  ensures DecodeRle(res + [(c, cnt)]) == DecodeRle(res) + Repeat(c, cnt)
  decreases |res|
{
  if |res| == 0 {
  } else {
    DecodeRle_Append(res[1..], c, cnt);
  }
}

/* helper modified by LLM (iteration 5): SliceIsRepeat lemma */
lemma SliceIsRepeat(s: seq<char>, i: int, c: char, cnt: nat)
  requires 0 <= i && i <= |s|
  requires 0 <= cnt && cnt <= |s| - i
  requires forall k :: 0 <= k && k < cnt ==> s[i + k] == c
  ensures s[i..i+cnt] == Repeat(c, cnt)
  decreases cnt
{
  if cnt == 0 {
  } else {
    SliceIsRepeat(s, i, c, cnt - 1);
  }
}

// </vc-helpers>

// <vc-spec>
method RunLengthEncode(s: seq<char>) returns (result: seq<(char, nat)>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i].1 > 0
    ensures
        forall i :: 0 <= i < |result| ==> i + 1 < |result| ==> result[i].0 != result[i + 1].0
    ensures
        DecodeRle(result) == s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): run-length encode implementation using inner loop without && */
  var res: seq<(char, nat)> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i && i <= |s|
    invariant forall k :: 0 <= k && k < |res| ==> res[k].1 > 0
    invariant forall k :: 0 <= k && k + 1 < |res| ==> res[k].0 != res[k+1].0
    invariant DecodeRle(res) == s[..i]
  {
    var c := s[i];
    var cnt: nat := 1;
    while i + cnt < |s|
      invariant 1 <= cnt && cnt <= |s| - i
      invariant forall k :: 0 <= k && k < cnt ==> s[i + k] == c
    {
      if s[i + cnt] == c {
        cnt := cnt + 1;
      } else {
        break;
      }
    }
    var oldRes := res;
    res := oldRes + [(c, cnt)];
    SliceIsRepeat(s, i, c, cnt);
    DecodeRle_Append(oldRes, c, cnt);
    i := i + cnt;
  }
  result := res;
}

// </vc-code>
