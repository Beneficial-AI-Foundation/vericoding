// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
function FlattenPairs(pairs: seq<(char, nat)>): seq<char>
  decreases |pairs|
{
  if |pairs| == 0 then
    []
  else
    var pair := pairs[0];
    var char := pair.0;
    var count := pair.1;
    [char] * count + FlattenPairs(pairs[1..])
}

predicate ValidRleSequence(seq: seq<(char, nat)>)
  ensures ValidRleSequence(seq) == (
    (forall i :: 0 <= i < |seq| ==> seq[i].1 > 0) &&
    (forall i :: 0 <= i < |seq| - 1 ==> seq[i].0 != seq[i + 1].0)
  )
{
  (forall i :: 0 <= i < |seq| ==> seq[i].1 > 0) &&
  (forall i :: 0 <= i < |seq| - 1 ==> seq[i].0 != seq[i + 1].0)
}

/* helper modified by LLM (iteration 3): Fixed function parameter access and added explicit tuple field access */
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
  /* code modified by LLM (iteration 3): Fixed compilation errors and added proper implementation */
  result := [];
  if |s| == 0 {
    return;
  }
  
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ValidRleSequence(result)
    invariant FlattenPairs(result) == s[0..i]
    invariant result == [] || (i < |s| ==> result[|result|-1].0 != s[i])
  {
    var currentChar := s[i];
    var count := 1;
    
    while i + count < |s| && s[i + count] == currentChar
      invariant i + count <= |s|
      invariant count >= 1
      invariant forall j :: i <= j < i + count ==> s[j] == currentChar
    {
      count := count + 1;
    }
    
    var temp := result;
    result := temp + [(currentChar, count)];
    i := i + count;
  }
}
// </vc-code>
