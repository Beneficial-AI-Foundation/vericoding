// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): filtering function and lemmas to relate FilterPos to the source sequence */
function FilterPos(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] > 0 then [s[0]] + FilterPos(s[1..])
  else FilterPos(s[1..])
}

lemma FilterPosAllPositive(s: seq<int>)
  ensures forall i:int :: 0 <= i && i < |FilterPos(s)| ==> FilterPos(s)[i] > 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    FilterPosAllPositive(s[1..]);
    if s[0] > 0 {
    } else {
    }
  }
}

lemma FilterPosPrefixElems(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  ensures forall k:int :: 0 <= k && k < |FilterPos(s[..n])| ==> (exists j:int :: 0 <= j && j < n && s[j] == FilterPos(s[..n])[k])
  decreases n
{
  if n == 0 {
  } else {
    FilterPosPrefixElems(s, n - 1);
    if s[n-1] > 0 {
    } else {
    }
  }
}

lemma FilterPosPrefixCoversPositive(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  ensures forall j:int :: 0 <= j && j < n && s[j] > 0 ==> (exists k:int :: 0 <= k && k < |FilterPos(s[..n])| && FilterPos(s[..n])[k] == s[j])
  decreases n
{
  if n == 0 {
  } else {
    FilterPosPrefixCoversPositive(s, n - 1);
    if s[n-1] > 0 {
    } else {
    }
  }
}

lemma FilterPosLenLe(s: seq<int>)
  ensures |FilterPos(s)| <= |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    FilterPosLenLe(s[1..]);
    if s[0] > 0 {
    } else {
    }
  }
}
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)

    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): filter with prefix invariant and use helper lemmas to discharge postconditions */
  var i := 0;
  result := [];
  while i < |l|
    invariant 0 <= i <= |l|
    invariant result == FilterPos(l[..i])
    decreases |l| - i
  {
    if l[i] > 0 {
      result := result + [l[i]];
    }
    i := i + 1;
  }
  // result == FilterPos(l)
  FilterPosAllPositive(l);
  FilterPosPrefixCoversPositive(l, |l|);
  FilterPosPrefixElems(l, |l|);
  FilterPosLenLe(l);
}
// </vc-code>
